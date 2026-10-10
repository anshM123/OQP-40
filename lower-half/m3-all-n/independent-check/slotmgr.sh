#!/bin/bash
# runs the remaining jobs with at most 2 of my compute processes at a time (counts running iv_* python processes)
export OMP_NUM_THREADS=1
PY="${PY:-python}"
cd "$(dirname "$0")"
running() { powershell -NoProfile -Command "(Get-CimInstance Win32_Process -Filter \"Name='python.exe'\" | Where-Object { \$_.CommandLine -like '*Python312*iv_*' -or (\$_.CommandLine -like '*iv_*' -and \$_.CommandLine -notlike '*venv*') }).Count" | tr -d '\r'; }
while read -r log args; do
  [ -z "$log" ] && continue
  while [ "$(running)" -ge 2 ]; do sleep 20; done
  echo "$(date) start $log: $args" >> slotmgr.log
  nohup "$PY" $args > "$log" 2>&1 &
  sleep 30
done << 'JOBS'
ivs_S2_nubox.log iv_as_run.py nu 0 3 24 15/4 8 64 4 box
iv_T3_double.log iv_tail_run.py double 2 4 8
iv_T2_farstrip.log iv_tail_run.py farstrip 0 3 8 4 8
iv_T1_farreg.log iv_tail_run.py farreg 3 250 62 4 8
iv_T4_atail.log iv_tail_run.py atail 0 512 512 2 8
iv_W4_mix_3_16x3_375.log iv_bb2.py mix 3 16 3 15/4 52 12 8
iv_W5_nus2_3_16x375_16.log iv_bb2.py nus2 3 16 15/4 16 52 98 8
iv_W6_nus2_64_250x375_8.log iv_bb2.py nus2 64 250 15/4 8 93 34 8
iv_W7_nus2_120_250x8_16.log iv_bb2.py nus2 120 250 8 16 65 32 8
ivs_S3_nu.log iv_as_run.py nuc 0 3 6 15/2 515 16 4
JOBS
echo "$(date) all jobs started" >> slotmgr.log
