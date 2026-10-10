#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "RESULT" iv_V6_dstrip_14_32x175_250.log 2>/dev/null; do sleep 20; done
"$PY" iv_bb2.py nus 16 64 8 16 96 16 8 > iv_V8_16_64x8_16.log 2>&1
"$PY" iv_bb2.py nus 3 16 16 64 13 48 8 > iv_V9_3_16x16_64.log 2>&1
"$PY" iv_bb2.py nus 64 250 64 512 93 56 8 > iv_V7_64_250x64_512.log 2>&1
