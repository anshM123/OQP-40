#!/bin/bash
# usage: final_rule.sh n qd [bits]   -> rules/n{n}.json with a uniform pipeline (parity, RREF projection)
n=$1; qd=$2; bits=${3:-40}
PY="${PY:-python}"
export OMP_NUM_THREADS=2
cd "$(dirname "$0")"
if [ ! -f sol/n${n}_q${qd}_cpfinal.npz ]; then
  NBASE=${NBASE:-20} NADD=${NADD:-40} timeout 14400 "$PY" polyrule_cp.py $n $qd sol/n${n}_q${qd}_cpfinal.npz > logs/final_cp_n$n.log 2>&1
fi
PARITY=1 PROJ=rref timeout 43200 "$PY" exact_rule.py $n $qd sol/n${n}_q${qd}_cpfinal.npz $bits rules/n$n.json > logs/final_exact_n$n.log 2>&1
grep -E "iter" logs/final_cp_n$n.log | tail -1; grep -E "RESULT" logs/final_exact_n$n.log
