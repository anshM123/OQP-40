#!/bin/bash
# remaining small-d core of Theorem B' (own TJ code); starts when the W1 run has finished
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "RESULT" iv_W1_mix_3_8x0_3.log 2>/dev/null; do sleep 15; done
"$PY" iv_bb2.py nus2 16 64 15/4 8 24 34 8 > iv_W3_nus2_16_64x375_8.log 2>&1
"$PY" iv_bb2.py mix 3 16 3 15/4 52 12 8 > iv_W4_mix_3_16x3_375.log 2>&1
"$PY" iv_bb2.py nus2 3 16 15/4 16 52 98 8 > iv_W5_nus2_3_16x375_16.log 2>&1
"$PY" iv_bb2.py nus2 64 250 15/4 8 93 34 8 > iv_W6_nus2_64_250x375_8.log 2>&1
"$PY" iv_bb2.py nus2 120 250 8 16 65 32 8 > iv_W7_nus2_120_250x8_16.log 2>&1
