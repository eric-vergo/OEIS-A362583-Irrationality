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
# Challenge/ is deliberately NOT swept here: the comparator challenge
# (Challenge/Challenge.lean) restates the locked claims with `sorry` BY
# DESIGN — it is the comparator's input, not part of the proof.  The
# sorry/axiom gates below still cover the real library (A362583/ Audit/).
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
echo "== comparator =="
# The comparator (leanprover/comparator) certifies that the A362583 library
# proves the exact statements in the Challenge module (see comparator.json).
# It needs landrun + systemd-run (Linux-only) and lean4export, so it cannot
# run on macOS: probe for the toolchain and degrade gracefully — a missing
# Linux-only tool must NEVER fail this script.  Status artifact:
# challenge/comparator-status.json ("configured" until CI flips it).
COMPARATOR="${COMPARATOR_BIN:-$(command -v comparator || true)}"
if [[ -n "$COMPARATOR" ]] && command -v landrun >/dev/null 2>&1 \
    && command -v systemd-run >/dev/null 2>&1; then
  echo "comparator toolchain found ($COMPARATOR) — verifying comparator.json"
  if "$COMPARATOR" comparator.json; then
    cat > challenge/comparator-status.json <<EOF
{
  "status": "verified",
  "config": "comparator.json",
  "solution_module": "A362583",
  "theorem_names": ["A362583.irrational_x", "A362583.raceSum_not_linear"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "verified_at": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
  "note": "Comparator requires Linux (landrun/systemd-run); run on CI to flip status to verified."
}
EOF
    echo "comparator: VERIFIED (challenge/comparator-status.json updated)"
  else
    echo "FATAL: comparator ran and rejected the solution" >&2
    exit 1
  fi
else
  echo "comparator toolchain absent (Linux-only: landrun/systemd-run) — skipping"
  if [[ ! -f challenge/comparator-status.json ]]; then
    cat > challenge/comparator-status.json <<'EOF'
{
  "status": "configured",
  "config": "comparator.json",
  "solution_module": "A362583",
  "theorem_names": ["A362583.irrational_x", "A362583.raceSum_not_linear"],
  "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
  "verified_at": null,
  "note": "Comparator requires Linux (landrun/systemd-run); run on CI to flip status to verified."
}
EOF
  fi
  echo "comparator: status $(grep -o '"status": "[^"]*"' challenge/comparator-status.json || echo unknown)"
fi

echo
echo "check.sh: OK"
