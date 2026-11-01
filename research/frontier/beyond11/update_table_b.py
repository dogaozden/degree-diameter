#!/usr/bin/env python3
"""update_table_b.py (job beyond-d11b): splice the rows of cells_b.txt into research/frontier/beyond/BEYOND_TABLE.md.
Only cells whose solution has a VALID haarcheck_gen log (runs/<stem>.gen.txt) are written. Cells already in the table
are replaced; new cells (Δ >= 15 at D = 11, Δ >= 14 at D = 12) go right after the largest existing row of their D."""
import math, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
TAB = os.path.join(HERE, '..', 'beyond', 'BEYOND_TABLE.md')
def moore(d, D): return 2 * sum((d - 1) ** i for i in range(D))
def W(d, D):
    if D % 2 == 0: return sum(d * (d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def n_at_mu(d, D, mu):
    w = W(d, D); lo, hi = 1.0, 1e17
    for _ in range(300):
        mid = math.sqrt(lo * hi)
        if mid * math.exp(-w / mid) < mu: lo = mid
        else: hi = mid
    return lo
rows = {}
for line in open(os.path.join(HERE, 'cells_b.txt')):
    if not line.strip() or line.startswith('#'): continue
    cell, stem, note = [x.strip() for x in line.split('|', 2)]
    d, D = map(int, cell.split(','))
    gen = os.path.join(HERE, 'runs', stem + '.gen.txt')
    if not (os.path.exists(gen) and any(l.startswith('VALID') for l in open(gen))):
        print('not yet VALID:', cell, stem); continue
    hdr = open(os.path.join(HERE, 'sols', stem + '.txt')).readline().split()
    N = int(hdr[hdr.index('N') + 1]); v = 2 * N
    mu = N * math.exp(-W(d, D) / N)
    rows[(d, D)] = (f'| ({d},{D}) | **{v:,}** | {100 * v / moore(d, D):.2f} | {moore(d, D) - 6:,} | {note}; mu = {mu:.2f} | '
                    f'haarcheck_gen VALID (research/frontier/runs/cloudcheck/{stem}.gen.txt) | '
                    f'Haar size law at mu = 5: 2N = {2 * n_at_mu(d, D, 5):.3g} |')
lines = open(TAB).read().split('\n')
def key(l):
    m = re.match(r'\| \((\d+),(\d+)\) \|', l)
    return (int(m.group(1)), int(m.group(2))) if m else None
out, done = [], set()
for i, l in enumerate(lines):
    k = key(l)
    out.append(rows[k] if k in rows else l)
    if k in rows: done.add(k)
    if k and k[1] in (11, 12):
        nxt = key(lines[i + 1]) if i + 1 < len(lines) else None
        if not nxt or nxt[1] != k[1]:          # last row of this D: append the new cells of this D
            for d in range(k[0] + 1, 40):
                if (d, k[1]) in rows and (d, k[1]) not in done: out.append(rows[(d, k[1])]); done.add((d, k[1]))
open(TAB, 'w').write('\n'.join(out))
print('rows written:', sorted(done)); print('missing:', sorted(set(rows) - done))
