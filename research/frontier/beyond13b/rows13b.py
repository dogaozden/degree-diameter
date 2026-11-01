#!/usr/bin/env python3
"""rows13b.py: BEYOND_TABLE rows for the cells raised by job beyond-d13b. cells.txt lines:
  cell | vertices | solution (research/frontier/sols/<file>) | check log (research/frontier/beyond13b/<path>) | note
A line counts only if its check log has a VALID line. The largest checked value per cell gives the row."""
import math, os
def moore(d, D): return 2 * sum((d - 1) ** i for i in range(D))
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def n_at_mu(d, D, mu):
    w = W(d, D); lo, hi = 1.0, 1e16
    for _ in range(300):
        mid = math.sqrt(lo * hi)
        if mid * math.exp(-w / mid) < mu: lo = mid
        else: hi = mid
    return lo
def mu_of(d, D, N): return N * math.exp(-W(d, D) / N)
def valid(path):
    return os.path.exists(path) and any(l.startswith('VALID') or 'RESULT VALID' in l
                                        for l in open(path, errors='replace'))
rows = {}
for line in open('cells.txt'):
    if not line.strip() or line.startswith('#'): continue
    cell, v, sol, chk, note = [x.strip() for x in line.split('|', 4)]
    d, D = map(int, cell.split(',')); v = int(v.replace(',', ''))
    if not valid(chk): continue
    if (d, D) in rows and rows[(d, D)][0] >= v: continue
    rows[(d, D)] = (v, f'{note}; mu = {mu_of(d, D, v // 2):.2f}',
                    f'research/frontier/beyond13b/{chk} (solution research/frontier/sols/{sol})')
for (d, D) in sorted(rows, key=lambda c: (c[1], c[0])):
    v, note, chk = rows[(d, D)]
    note = note.replace('x|_', 'x\\|_')
    print(f'| ({d},{D}) | **{v:,}** | {100*v/moore(d,D):.2f} | {moore(d,D)-6:,} | {note} | {chk} | '
          f'Haar size law at mu = 5: 2N = {2*n_at_mu(d,D,5):.3g} |')
