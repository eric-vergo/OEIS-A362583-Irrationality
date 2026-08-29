#!/usr/bin/env bash
# Assert the shared definitions are byte-identical across the four modules.
#
# The comparator certifies that Solution proves the Challenge statement — it says
# nothing about whether the Challenge is the claim this project actually makes.
# comparator/Challenge.lean and comparator/Solution.lean each re-declare
# oddPrime / bit / ϱ from scratch (Solution must not import Challenge: they are
# elaborated in separate environments), and both are supposed to be
# byte-identical copies of A362583/Defs.lean. Solution.lean's
# `ϱ_eq : ϱ = A362583.ϱ := rfl` catches drift on the solution side; NOTHING
# catches drift on the challenge side, where it would quietly weaken the
# certified claim. This script is that missing check. SolutionProbe.lean is held
# to the same standard: if it stopped being a faithful copy of the solution, the
# CI sandbox's denied-write probe would stop testing what it claims to.
#
# This is the consumer's own `build_check_script` hook in the shared CI standard
# (eric-vergo/Showcase `.github/workflows/blueprint-verify.yml`): it runs in the
# TRUSTED build job, which reads the four files and never elaborates them. It
# reads only source text, so it also runs on a workstation from the repository
# root.
set -euo pipefail

# `$RUNNER_TEMP` on a runner; anywhere writable off one, so the same script is
# the local check and the CI check.
scratch="${RUNNER_TEMP:-${TMPDIR:-/tmp}}"

# `index($0, s) == 1` is a byte-exact prefix test — no regex engine, so the
# multibyte identifiers (ϱ, ℝ, ℕ) are compared as bytes and the extraction
# cannot drift with the awk implementation or the locale.
extract() {
  awk '
    index($0, "/-- The `k`-th odd prime: `oddPrime 0 = 3`,") == 1 { inblock = 1 }
    inblock { print }
    inblock && index($0, "noncomputable def ϱ : ℝ := ") == 1 { exit }
  ' "$1"
}
for f in A362583/Defs.lean comparator/Challenge.lean comparator/Solution.lean \
         comparator/SolutionProbe.lean; do
  out="${scratch}/$(printf '%s' "$f" | tr / _).block"
  extract "$f" > "$out"
  lines="$(wc -l < "$out" | tr -d '[:space:]')"
  # 15 = three docstring+definition pairs plus the two blank lines between them.
  # Anything else means an anchor moved and the diff below would be comparing
  # the wrong thing.
  if [ "$lines" -ne 15 ]; then
    echo "definition-block extraction failed for $f: got $lines lines, expected 15"
    exit 1
  fi
done
diff "${scratch}/A362583_Defs.lean.block" "${scratch}/comparator_Challenge.lean.block"
diff "${scratch}/A362583_Defs.lean.block" "${scratch}/comparator_Solution.lean.block"
diff "${scratch}/A362583_Defs.lean.block" "${scratch}/comparator_SolutionProbe.lean.block"
echo "oddPrime / bit / ϱ are byte-identical across the four modules."
