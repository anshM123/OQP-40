#!/bin/sh
# Final region-A' runs (Taylor models with Cauchy bounds), two jobs.
PY="${PY:-python}"
P='[[0.0,0.3,0.3,0.6,0.025],[0.3,0.35,0.6,1.0,0.0125],[0.35,0.45,0.6,3.0,0.0125],[0.45,0.5,0.6,3.0,0.005]]'
export OMP_NUM_THREADS=1
"$PY" regionA_run.py runs/A_final_0.json "$P" 0 2 > runs/A_final_0.log 2>&1 &
"$PY" regionA_run.py runs/A_final_1.json "$P" 1 2 > runs/A_final_1.log 2>&1 &
wait
