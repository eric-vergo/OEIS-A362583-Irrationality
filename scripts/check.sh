#!/usr/bin/env bash
# check.sh — build + hygiene gate for the A362583 formalization.
# Usage: scripts/check.sh [--strict]
#   --strict : any sorry/admit/native_decide/axiom/maxHeartbeats hit is fatal.
set -uo pipefail

cd "$(dirname "$0")/.."

STRICT=0
if [[ "${1:-}" == "--strict" ]]; then
  STRICT=1
fi

echo "== lake build =="
if ! lake build; then
  echo "FATAL: lake build failed" >&2
  exit 1
fi

echo
echo "== hygiene grep (A362583/ Audit/) =="
PATTERNS=('\bsorry\b' '\badmit\b' '\bnative_decide\b' '^axiom' 'maxHeartbeats')
LABELS=('sorry' 'admit' 'native_decide' 'axiom' 'maxHeartbeats')
TOTAL=0
for i in "${!PATTERNS[@]}"; do
  HITS=$(grep -rEn "${PATTERNS[$i]}" --include='*.lean' A362583/ Audit/ 2>/dev/null)
  COUNT=0
  if [[ -n "$HITS" ]]; then
    COUNT=$(printf '%s\n' "$HITS" | wc -l | tr -d ' ')
  fi
  echo "${LABELS[$i]}: $COUNT"
  if [[ "$COUNT" -gt 0 ]]; then
    printf '%s\n' "$HITS"
    TOTAL=$((TOTAL + COUNT))
  fi
done

if [[ "$STRICT" -eq 1 && "$TOTAL" -gt 0 ]]; then
  echo "FATAL (--strict): $TOTAL hygiene hit(s)" >&2
  exit 1
fi

echo
echo "== axioms check =="
if [[ -s scripts/AxiomsCheck.lean ]] && grep -q '#print axioms' scripts/AxiomsCheck.lean; then
  AXOUT=$(lake env lean scripts/AxiomsCheck.lean 2>&1)
  STATUS=$?
  printf '%s\n' "$AXOUT"
  if [[ $STATUS -ne 0 ]]; then
    echo "FATAL: axioms check failed to run" >&2
    exit 1
  fi
  # Assert every reported axiom is in the allowed set (spec §7.2):
  # strip the declaration-name prefix, split the bracketed list, check each entry.
  BAD=$(printf '%s\n' "$AXOUT" | grep "depends on axioms" \
        | sed -E 's/^.*depends on axioms: \[//; s/\]$//' | tr ',' '\n' \
        | sed -E 's/^ +| +$//g' | sort -u \
        | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)
  if [[ -n "$BAD" ]]; then
    echo "FATAL: disallowed axiom(s) in output: $BAD" >&2
    exit 1
  fi
  if ! printf '%s\n' "$AXOUT" | grep -q "depends on axioms"; then
    echo "FATAL: axioms output missing 'depends on axioms' lines" >&2
    exit 1
  fi
else
  echo "scripts/AxiomsCheck.lean has no #print axioms yet — skipped"
fi

echo
echo "check.sh: OK"
