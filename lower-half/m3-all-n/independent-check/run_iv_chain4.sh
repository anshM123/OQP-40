#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "RESULT" iv_V7_64_250x64_512.log 2>/dev/null; do sleep 20; done
"$PY" iv_bb2.py mix 16 64 3 15/4 192 12 8 > iv_V11_mix_16_64x3_375.log 2>&1
"$PY" iv_bb2.py mix 8 64 0 3 224 48 8 > iv_V10_mix_8_64x0_3.log 2>&1
