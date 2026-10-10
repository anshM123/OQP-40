#!/bin/bash
# strip runs (own a-Taylor-model code); starts when the W2 run has finished
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
until grep -q "RESULT" iv_W2_mix_64_250x0_375.log 2>/dev/null; do sleep 15; done
"$PY" iv_as_run.py corner > ivs_S0_corner.log 2>&1
"$PY" iv_as_run.py direct 0 3 12 1/4 4 1/8 4 > ivs_S1_direct.log 2>&1
"$PY" iv_as_run.py nu 0 3 24 15/4 8 64 4 box > ivs_S2_nubox.log 2>&1
"$PY" iv_as_run.py nuc 0 3 6 15/2 515 16 4 > ivs_S3_nu.log 2>&1
