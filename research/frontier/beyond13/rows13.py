#!/usr/bin/env python3
"""rows13.py: BEYOND_TABLE rows for the beyond-d13 cells. Haar cells from cells.txt (sol stem in sols/, haarcheck_gen log
runs/<stem>.gen.txt), other graphs from cells_other.txt (vertices, edge list, check file). Prints one row per cell."""
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
rows = {}
for line in open('cells.txt'):
    if not line.strip() or line.startswith('#'): continue
    cell, stem, note = [x.strip() for x in line.split('|', 2)]
    d, D = map(int, cell.split(','))
    hdr = open(f'sols/{stem}.txt').readline().split(); N = int(hdr[hdr.index('N') + 1])
    log = f'runs/{stem}.gen.txt'
    if not (os.path.exists(log) and any(l.startswith('VALID') for l in open(log))): continue   # check pending
    if (d, D) in rows and rows[(d, D)][0] >= 2 * N: continue
    rows[(d, D)] = (2 * N, f'{note}; mu = {mu_of(d, D, N):.2f}',
                    f'haarcheck_gen VALID (research/frontier/runs/cloudcheck/{stem}.gen.txt)')
if os.path.exists('cells_other.txt'):
    for line in open('cells_other.txt'):
        if not line.strip() or line.startswith('#'): continue
        cell, v, edges, chk, note = [x.strip() for x in line.split('|', 4)]
        d, D = map(int, cell.split(',')); v = int(v)
        if (d, D) in rows and rows[(d, D)][0] >= v: continue
        if not any(l.startswith('VALID') or 'RESULT VALID' in l for l in open(f'checks/{chk}')): continue   # pending
        rows[(d, D)] = (v, f'{note}; mu = {mu_of(d, D, v // 2):.2f}',
                        f'research/frontier/beyond13/checks/{chk}' + (f' (graph research/frontier/beyond13/graphs/{edges})' if edges != '-' else ''))
for (d, D) in sorted(rows, key=lambda c: (c[1], c[0])):
    v, note, chk = rows[(d, D)]
    note = note.replace('x|_', 'x\\|_')   # a bare | would split the markdown table cell
    print(f'| ({d},{D}) | **{v:,}** | {100*v/moore(d,D):.2f} | {moore(d,D)-6:,} | {note} | {chk} | '
          f'Haar size law at mu = 5: 2N = {2*n_at_mu(d,D,5):.3g} |')
