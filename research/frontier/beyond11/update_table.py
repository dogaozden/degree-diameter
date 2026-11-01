#!/usr/bin/env python3
"""update_table.py: splice the beyond-d11 rows into research/frontier/beyond/BEYOND_TABLE.md.
For every line of cells.txt whose solution has a VALID haarcheck_gen log, write/replace the row of that cell.
New cells are inserted after the (10,11) / (10,12) rows; cells already in the table are replaced (the old value is
kept in the construction note of cells.txt)."""
import math, os, re
HERE = os.path.dirname(os.path.abspath(__file__))
TAB = os.path.join(HERE, '..', 'beyond', 'BEYOND_TABLE.md')
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
rows = {}
for line in open(os.path.join(HERE, 'cells.txt')):
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
lines = [l for l in lines if not (key(l) in rows and key(l)[0] >= 11)]   # rerun: drop earlier copies of the new cells
out = []
done = set()
for l in lines:
    k = key(l)
    if k in rows: out.append(rows[k]); done.add(k)
    else: out.append(l)
    if k in ((10, 11), (10, 12)):
        D = k[1]
        for d in range(11, 15):
            if (d, D) in rows and (d, D) not in done: out.append(rows[(d, D)]); done.add((d, D))
open(TAB, 'w').write('\n'.join(out))
print('rows written:', sorted(done)); print('missing:', sorted(set(rows) - done))
