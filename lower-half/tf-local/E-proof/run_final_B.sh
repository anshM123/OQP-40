#!/bin/sh
# Final region-B runs (rigorous interval verification), L = 10, exclusion = pieces of A'.
PY="${PY:-python}"
EX='[[0.0,0.3,0.3,0.6],[0.3,0.35,0.6,1.0],[0.35,0.45,0.6,3.0],[0.45,0.5,0.6,3.0]]'
MW='[0.00048828125,0.001953125,0.001953125]'
export OMP_NUM_THREADS=1
"$PY" regionB.py 0.0 0.3 10 runs/B_final_lo.json "$EX" "$MW" 3000000 > runs/B_final_lo.log 2>&1 &
"$PY" regionB.py 0.3 0.5 10 runs/B_final_hi.json "$EX" "$MW" 3000000 > runs/B_final_hi.log 2>&1 &
wait
