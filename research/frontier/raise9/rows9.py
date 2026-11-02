#!/usr/bin/env python3
"""rows9.py (job raise-d9): replace the (Δ,9) rows of research/frontier/beyond/BEYOND_TABLE.md for the cells in
cells9.txt ("d | stem | note"), using only finds whose haarcheck_gen log checks/<stem>.gen.txt says VALID.
The solution file is sols/<stem>.txt (copied to research/frontier/sols/)."""
import math, os, re
HERE = os.path.dirname(os.path.abspath(__file__)); TAB = os.path.join(HERE, '..', 'beyond', 'BEYOND_TABLE.md')
def moore(d, D): return 2 * sum((d - 1) ** i for i in range(D))
def W(d, D): return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))
def n_at_mu(d, D, mu):
    w = W(d, D); lo, hi = 1.0, 1e17
    for _ in range(300):
        mid = math.sqrt(lo * hi)
        if mid * math.exp(-w / mid) < mu: lo = mid
        else: hi = mid
    return lo
rows = {}
for line in open(os.path.join(HERE, 'cells9.txt')):
    if not line.strip() or line.startswith('#'): continue
    d, stem, note = [x.strip() for x in line.split('|', 2)]; d = int(d); D = 9
    log = os.path.join(HERE, 'checks', stem + '.gen.txt')
    if not (os.path.exists(log) and any(l.startswith('VALID') for l in open(log))): print('not VALID yet:', d, stem); continue
    hdr = open(os.path.join(HERE, 'sols', stem + '.txt')).readline().split(); N = int(hdr[hdr.index('N') + 1]); v = 2 * N
    mu = N * math.exp(-W(d, D) / N)
    rows[d] = (f'| ({d},{D}) | **{v:,}** | {100 * v / moore(d, D):.2f} | {moore(d, D) - 6:,} | {note}; mu = {mu:.2f} | '
               f'haarcheck_gen VALID (research/frontier/raise9/checks/{stem}.gen.txt) | Haar size law at mu = 5: 2N = {2 * n_at_mu(d, D, 5):.3g} |')
out = []
for l in open(TAB).read().split('\n'):
    m = re.match(r'\| \((\d+),9\) \|', l)
    out.append(rows[int(m.group(1))] if m and int(m.group(1)) in rows else l)
open(TAB, 'w').write('\n'.join(out)); print('rows written:', sorted(rows))
