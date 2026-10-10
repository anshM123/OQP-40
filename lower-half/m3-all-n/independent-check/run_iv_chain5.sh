#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "RESULT" iv_V10_mix_8_64x0_3.log 2>/dev/null; do sleep 20; done
"$PY" iv_bb2.py nus 50 120 60 64 70 4 8 > iv_V12_50_120x60_64.log 2>&1
