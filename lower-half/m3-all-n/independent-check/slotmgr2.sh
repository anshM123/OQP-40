#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
running() { powershell -NoProfile -Command "(Get-CimInstance Win32_Process -Filter \"Name='python.exe'\" | Where-Object { \$_.CommandLine -like '*Python312*iv_*' }).Count" | tr -d '\r'; }
until grep -q "all jobs started" slotmgr.log 2>/dev/null; do sleep 30; done
sleep 40
while [ "$(running)" -ge 2 ]; do sleep 20; done
echo "$(date) start iv_T3_double.log (rerun after the 0/0 fix)" >> slotmgr.log
"$PY" iv_tail_run.py double 2 4 8 > iv_T3_double.log 2>&1
