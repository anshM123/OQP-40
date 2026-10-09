#!/usr/bin/env bash
# Check the whole development from scratch, one file at a time, in dependency order (BUILD_ORDER.txt).
# Run from this folder after fetching the prebuilt Mathlib of the pinned revision:
#     lake exe cache get
#     bash check.sh
# Each file is elaborated and kernel-checked by `lake env lean`; its .olean goes to .lake/build so that later files can
# import it. OQP40/Axioms.lean and OQP40/AxiomsThm33.lean print `#print axioms` for the main theorems. Logs go to
# logs_check/.
set -uo pipefail
out=.lake/build/lib/lean
mkdir -p "$out/OQP27" "$out/HarmonicMajorization" "$out/OQP40" logs_check
echo "== keyword scan (code lines only; docstrings mention 'no sorry') =="
grep -n -E "^\s*(axiom|sorry)\b|\bsorry\b\s*$|native_decide|\badmit\b" OQP27/*.lean HarmonicMajorization/*.lean \
  OQP40/*.lean || echo "none"
while read -r m; do
  m="$(printf '%s' "$m" | tr -d '\r')"; [ -z "$m" ] && continue
  f="${m//./\/}"; log="logs_check/${m}.log"; t0=$(date +%s)
  if [[ "$f" == *Axioms* ]]; then
    lake env lean "$f.lean" > "$log" 2>&1
  else
    lake env lean -o "$out/$f.olean" -i "$out/$f.ilean" "$f.lean" > "$log" 2>&1
  fi
  code=$?
  printf '%-40s exit=%d %5ds\n' "$m" "$code" "$(( $(date +%s) - t0 ))"
  if [ $code -ne 0 ]; then echo "FAILED: $m (see $log)"; exit 1; fi
done < BUILD_ORDER.txt
echo "== axioms (every line below must end with [propext, Classical.choice, Quot.sound]) =="
grep "depends on axioms" logs_check/OQP40.Axioms.log
echo "== axioms of Theorem 1 of the lower-half note (OQP40/AxiomsThm33.lean) =="
grep "depends on axioms" logs_check/OQP40.AxiomsThm33.log
echo "== nonstandard axiom lines (should be empty) =="
cat logs_check/OQP40.Axioms.log logs_check/OQP40.AxiomsThm33.log | grep "depends on axioms" \
  | grep -v "\[propext, Classical.choice, Quot.sound\]" || echo "none"
