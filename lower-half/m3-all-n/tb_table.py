"""Collect the Theorem B verification logs into a markdown table (tb_table.md)."""
import re, os
RUNS = [
    ('C3 stationary tail', 'a >= 64, 0 <= d <= 64', 'tb_tail2_A64.log'),
    ('C3 stationary tail', 'a >= 64, 64 <= d <= 512', 'tb_tail2_A64_far.log'),
    ('C5 double tail', 'a >= 64, d >= 512', 'tb_ddouble.log'),
    ('C4 far tail', '3 <= a <= 64, d >= 512', 'tb_dtail.log'),
    ('C1 core', '3 <= a <= 16, 3 <= d <= 16', 'tb_core_A1.log'),
    ('C1 core', '16 <= a <= 64, 16 <= d <= 64', 'tb_core_A2a_hi.log'),
    ('C1 core', '16 <= a <= 64, 15/4 <= d <= 16', 'tb_core_A2a_lo1.log'),
    ('C1 (mixed form)', '16 <= a <= 40, 3 <= d <= 15/4', 'tb_core_lo2_16_40.log'),
    ('C1 (mixed form)', '40 <= a <= 64, 3 <= d <= 15/4', 'tb_core_lo2_40_64.log'),
    ('C1 core', '3 <= a <= 16, 16 <= d <= 64', 'tb_core_A2b.log'),
    ('C1 core', '3 <= a <= 64, 64 <= d <= 512', 'tb_core_far.log'),
    ('C2 d-strip', '3 <= a <= 8, 0 <= d <= 3', 'tb_dstrip_3_8.log'),
    ('C2 d-strip', '8 <= a <= 13, 0 <= d <= 3', 'tb_dstrip_8_13.log'),
    ('C2 d-strip', '13 <= a <= 18, 0 <= d <= 3', 'tb_dstrip_13_18.log'),
    ('C2 d-strip', '18 <= a <= 23, 0 <= d <= 3', 'tb_dstrip_18_23.log'),
    ('C2 d-strip', '23 <= a <= 28, 0 <= d <= 3', 'tb_dstrip_23_28.log'),
    ('C2 d-strip', '28 <= a <= 33, 0 <= d <= 3', 'tb_dstrip_28_33.log'),
    ('C2 d-strip', '33 <= a <= 48, 0 <= d <= 3', 'tb_dstrip_33_48.log'),
    ('C2 d-strip', '48 <= a <= 64, 0 <= d <= 3', 'tb_dstrip_48_64.log'),
]
rows = ['| chart | region (all eps in [0, 1/37]) | log | boxes / cells | time (s) | result |', '|---|---|---|---|---|---|']
for name, region, log in RUNS:
    if not os.path.exists(log):
        rows.append(f'| {name} | {region} | `{log}` | | | not run |')
        continue
    s = open(log).read()
    m = re.search(r'(boxes accepted|cells): (\d+), failures: (\d+), time ([\d.]+) s', s)
    res = 'VERIFIED' if 'RESULT: REGION VERIFIED' in s else ('FAILED' if 'RESULT: FAILED' in s else 'running/incomplete')
    if m:
        rows.append(f'| {name} | {region} | `{log}` | {m.group(2)} | {m.group(4)} | {res} |')
    else:
        prog = re.findall(r'progress: (\d+) boxes', s)
        rows.append(f'| {name} | {region} | `{log}` | {prog[-1] if prog else 0} so far | | {res} |')
open('tb_table.md', 'w').write('\n'.join(rows) + '\n')
print('\n'.join(rows))
