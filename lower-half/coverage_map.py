"""Coverage map of the lower half (LH) of OQP 40: which (n, m), 1 <= n, m <= NMAX, are proved (any dimension).
Writes a plain SVG (standard library only).
Usage: python coverage_map.py out.svg N3 N4
  N3, N4: comma-separated lists of n for which Conjecture F is proved at (n,3), resp. (n,4)."""
import sys

out = sys.argv[1]
N3 = set(int(v) for v in sys.argv[2].split(',') if v)
N4 = set(int(v) for v in sys.argv[3].split(',') if v)
NMAX = 16
SOS = {(3, 4), (4, 3), (4, 4), (4, 6), (6, 4)}
COL = {'classical': '#cfd3d6', 'earlier': '#85c1e9', 'm3': '#2e86c1', 'm4': '#1a5276', 'open': '#ffffff'}
LABEL = {'classical': 'min(n, m) ≤ 2 (elementary)',
         'earlier': '(3,3) and the sum-of-squares cases (note 04)',
         'm3': '(n,3) and (3,n) (note 05)',
         'm4': '(n,4) and (4,n) (note 06)',
         'open': 'open'}


def status(n, m):
    if min(n, m) <= 2:
        return 'classical'
    if (n, m) == (3, 3) or (n, m) in SOS:
        return 'earlier'
    if (m == 3 and n in N3) or (n == 3 and m in N3):
        return 'm3'
    if (m == 4 and n in N4) or (n == 4 and m in N4):
        return 'm4'
    return 'open'


cell = 28
x0, y0 = 60, 40
W = x0 + NMAX * cell + 30
H = y0 + NMAX * cell + 175
parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}" '
         f'font-family="Helvetica, Arial, sans-serif">',
         f'<rect width="{W}" height="{H}" fill="#ffffff"/>',
         f'<text x="{W/2}" y="22" text-anchor="middle" font-size="14" font-weight="bold">'
         f'Lower half of OQP 40: proved cases, any dimension</text>']
for n in range(1, NMAX + 1):
    for m in range(1, NMAX + 1):
        x = x0 + (n - 1) * cell
        y = y0 + (NMAX - m) * cell   # m increases upwards
        parts.append(f'<rect x="{x}" y="{y}" width="{cell}" height="{cell}" fill="{COL[status(n, m)]}" '
                     f'stroke="#7b7d7d" stroke-width="0.6"><title>(n,m) = ({n},{m}): {LABEL[status(n, m)]}</title></rect>')
# axes labels
for k in range(1, NMAX + 1):
    parts.append(f'<text x="{x0 + (k - 0.5) * cell}" y="{y0 + NMAX * cell + 16}" text-anchor="middle" font-size="10">{k}</text>')
    parts.append(f'<text x="{x0 - 8}" y="{y0 + (NMAX - k + 0.5) * cell + 4}" text-anchor="end" font-size="10">{k}</text>')
parts.append(f'<text x="{x0 + NMAX * cell / 2}" y="{y0 + NMAX * cell + 34}" text-anchor="middle" font-size="12">'
             f'n (number of letters A)</text>')
parts.append(f'<text x="18" y="{y0 + NMAX * cell / 2}" text-anchor="middle" font-size="12" '
             f'transform="rotate(-90 18 {y0 + NMAX * cell / 2})">m (number of letters B)</text>')
# (5,5) marker
x55 = x0 + 4 * cell
y55 = y0 + (NMAX - 5) * cell
parts.append(f'<rect x="{x55}" y="{y55}" width="{cell}" height="{cell}" fill="none" stroke="#c0392b" stroke-width="2.5"/>')
parts.append(f'<text x="{x55 + cell + 6}" y="{y55 - 6}" font-size="10" fill="#c0392b">(5,5): the upper half fails here '
             f'(Cha–Lee); the lower half is open</text>')
# legend
ly = y0 + NMAX * cell + 52
for k, key in enumerate(['classical', 'earlier', 'm3', 'm4', 'open']):
    yy = ly + k * 22
    parts.append(f'<rect x="{x0}" y="{yy}" width="16" height="16" fill="{COL[key]}" stroke="#7b7d7d" stroke-width="0.6"/>')
    parts.append(f'<text x="{x0 + 24}" y="{yy + 12}" font-size="11">{LABEL[key]}</text>')
parts.append('</svg>')
open(out, 'w', encoding='utf-8').write('\n'.join(parts) + '\n')
print('wrote', out)
