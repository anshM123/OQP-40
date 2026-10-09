#!/bin/bash
# independent checks on the final rule files: verify_independent (sympy) and check_rule (matrices, 50 digits)
PY="${PY:-python}"
export OMP_NUM_THREADS=1
cd "$(dirname "$0")"
for n in "$@"; do
  timeout 20000 "$PY" verify_independent.py rules/n$n.json > logs/final_indep_n$n.log 2>&1
  echo "n=$n independent: $(grep -E 'INDEPENDENT' logs/final_indep_n$n.log)"
  timeout 20000 "$PY" check_rule.py rules/n$n.json 6 3 > logs/final_check_n$n.log 2>&1
  echo "n=$n end-to-end: $(grep SUMMARY logs/final_check_n$n.log)"
done
