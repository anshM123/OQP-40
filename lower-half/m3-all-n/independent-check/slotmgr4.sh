#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
running() { powershell -NoProfile -Command "(Get-CimInstance Win32_Process -Filter \"Name='python.exe'\" | Where-Object { \$_.CommandLine -like '*Python312*iv_*' }).Count" | tr -d '\r'; }
until grep -q "start iv_T1_farreg.log (rerun" slotmgr.log 2>/dev/null; do sleep 30; done
sleep 60
while [ "$(running)" -ge 2 ]; do sleep 20; done
echo "$(date) start iv_T4_atail.log (rerun after the S_of fix)" >> slotmgr.log
"$PY" iv_tail_run.py atail 0 512 512 2 8 > iv_T4_atail.log 2>&1
