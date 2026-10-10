#!/bin/bash
# my verifier, further regions of Theorem B' (eps in [0, 1/37]); starts after PID $1 has exited
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "gradient checks" soundness_dual_mixed3.log 2>/dev/null; do sleep 20; done
"$PY" iv_bb2.py nus 16 50 16 64 34 48 8 > iv_V2_16_50x16_64.log 2>&1
"$PY" iv_bb2.py nus 3 64 64 512 61 56 8 > iv_V4_3_64x64_512.log 2>&1
"$PY" iv_bb2.py nus 50 120 8 25 70 68 8 > iv_V5_50_120x8_25.log 2>&1
"$PY" iv_bb2.py nus 120 250 16 64 130 48 8 > iv_V3_120_250x16_64.log 2>&1
