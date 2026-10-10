"""Table of the strip runs (Theorem B'', RESULTS.md 8.4) from their logs.  Usage: python tb_sx_table.py > tb_sx_table.md"""
import re

RUNS = [
    ('S0 corner', '0 <= a <= 1/4, 0 <= b <= 1/4', 'tb_sx_corner.log'),
    ('S1 direct', '0 <= a <= 3 (12 strips), 1/4 <= b <= x0 + 4', 'tb_sx_direct.log'),
    ('S2 nu, --box', '0 <= a <= 3/2 (12 strips of 1/8), y1 + 15/4 <= b <= 15/2', 'tb_sx_nu_low_a.log'),
    ('S2 nu, --box', '3/2 <= a <= 3 (12 strips of 1/8), y1 + 15/4 <= b <= 15/2', 'tb_sx_nu_low_b.log'),
    ('S3 nu', '0 <= a <= 3 (6 strips), 15/2 <= b <= 515', 'tb_sx_nu.log'),
    ('S4 far tail', '0 <= a <= 3, d >= 512', 'tb_sx_dtail.log'),
]

print('| chart | region (all eps in [0, 1/37]) | log | boxes | time (s) | certified lower bounds | result |')
print('|---|---|---|---|---|---|---|')
tot_b, tot_t = 0, 0.0
for name, region, log in RUNS:
    try:
        txt = open(log, encoding='utf-8').read()
    except OSError:
        print(f'| {name} | {region} | `{log}` | - | - | - | MISSING |')
        continue
    m = re.search(r'boxes accepted: (\d+).*?time ([\d.]+) s', txt)
    boxes, t = (int(m.group(1)), float(m.group(2))) if m else (0, 0.0)
    tot_b += boxes
    tot_t += t
    lows = re.findall(r'certified min lower bound of ([\w ]+): ([-\d.e+]+)', txt)
    lb = ', '.join(f'{k.strip()} >= {float(v):.4g}' for k, v in lows)
    res = 'VERIFIED' if 'RESULT: REGION VERIFIED' in txt else 'FAILED'
    print(f'| {name} | {region} | `{log}` | {boxes} | {t:.1f} | {lb} | {res} |')
print(f'\nTotal: {tot_b} boxes, {tot_t:.0f} s.')
