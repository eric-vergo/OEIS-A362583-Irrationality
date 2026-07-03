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
  if ! lake env lean scripts/AxiomsCheck.lean; then
    echo "FATAL: axioms check failed" >&2
    exit 1
  fi
else
  echo "scripts/AxiomsCheck.lean has no #print axioms yet — skipped"
fi

echo
echo "check.sh: OK"
