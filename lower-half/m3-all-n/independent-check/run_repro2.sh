#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "RESULT" rerun_orig/tb_tail2_A64.log 2>/dev/null; do sleep 20; done
cd ..
"$PY" tb_bb.py --dual mixed3 8 13 0 3 0 1 1 37 5 6 > independent-check/rerun_orig/tb_dstrip_8_13.log 2>&1
