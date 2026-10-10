#!/bin/bash
cd "$(dirname "$0")"
echo "== my verifier (iv_*.log)"; for f in iv_R1_critical.log iv_V*.log; do [ -f $f ] && echo "$f: $(head -1 $f | sed 's/independent verifier (centre\/box jets): //') | $(grep 'boxes accepted' $f) | $(grep 'lower bound of L3' $f | sed 's/ on box.*//') | $(grep RESULT $f)"; done
echo "== corrected mixed3 re-run"; grep -E "^region|boxes accepted|RESULT" rerun_mixed3_fixed.log
echo "== S3 re-run"; grep -E "boxes accepted|RESULT|bound" rerun_S3_const.log 2>/dev/null
echo "== reproduction of original runs"; for f in rerun_orig/*.log; do b=$(basename $f); diff <(grep -v "time\|progress" ../$b) <(grep -v "time\|progress" $f) > /dev/null && echo "$b: identical (timing/progress lines excluded)" || echo "$b: DIFFERS"; done
echo "== soundness / samples"; tail -1 soundness_dual.log soundness_dual_nu2.log soundness_dual_mixed3.log soundness_sx.log soundness_sx_big.log 2>/dev/null; grep "samples:" sample_defs_*.log
