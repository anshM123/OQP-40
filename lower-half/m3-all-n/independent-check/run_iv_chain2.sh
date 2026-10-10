#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "RESULT" iv_V3_120_250x16_64.log 2>/dev/null; do sleep 20; done
"$PY" iv_bb2.py mix 14 32 7/4 5/2 144 12 8 > iv_V6_dstrip_14_32x175_250.log 2>&1
