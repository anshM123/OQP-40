#!/bin/bash
# after the corrected mixed3 re-run: S3 re-run with the current code, then reproduction runs of two original logs
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until [ "$(grep -c RESULT rerun_mixed3_fixed.log)" -ge 10 ]; do sleep 30; done
"$PY" rerun_S3_const.py > rerun_S3_const.log 2>&1
cd ..
"$PY" tb_sx_run.py --box nu 3/2 3 15/4 15/2 12 64 4 > independent-check/rerun_orig/tb_sx_nu_low_b.log 2>&1
"$PY" tb_tail2.py 64 0 64 2 4 > independent-check/rerun_orig/tb_tail2_A64.log 2>&1
