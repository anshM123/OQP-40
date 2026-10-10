#!/bin/bash
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
running() { powershell -NoProfile -Command "(Get-CimInstance Win32_Process -Filter \"Name='python.exe'\" | Where-Object { \$_.CommandLine -like '*Python312*iv_*' }).Count" | tr -d '\r'; }
until grep -q "rerun after the 0/0 fix" slotmgr.log 2>/dev/null; do sleep 30; done
sleep 60
for job in "iv_T2_farstrip.log farstrip 0 3 8 4 8" "iv_T1_farreg.log farreg 3 250 62 4 8"; do
  set -- $job
  log=$1; shift
  while [ "$(running)" -ge 2 ]; do sleep 20; done
  echo "$(date) start $log (rerun, patched log forms)" >> slotmgr.log
  nohup "$PY" iv_tail_run.py "$@" > "$log" 2>&1 &
  sleep 40
done
