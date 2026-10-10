#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "RESULT" rerun_orig/tb_dstrip_8_13.log 2>/dev/null; do sleep 20; done
"$PY" soundness_sx.py 300 8 17 > soundness_sx_big.log 2>&1
