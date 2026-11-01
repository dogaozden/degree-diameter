#!/usr/bin/env python3
"""rows.py: BEYOND_TABLE rows for the beyond-d11 cells from a small list (cell, sol stem, construction note)."""
import math, sys
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
for line in open(sys.argv[1]):
    if not line.strip() or line.startswith('#'): continue
    cell, stem, note = [x.strip() for x in line.split('|')]
    d, D = map(int, cell.split(','))
    hdr = open(f'sols/{stem}.txt').readline().split()
    N = int(hdr[hdr.index('N') + 1]); v = 2 * N
    ub = moore(d, D) - 6
    chk = f'haarcheck_gen VALID (research/frontier/runs/cloudcheck/{stem}.gen.txt)'
    print(f'| ({d},{D}) | **{v:,}** | {100*v/moore(d,D):.2f} | {ub:,} | {note}; mu = {mu_of(d,D,N):.2f} | {chk} | '
          f'Haar size law at mu = 5: 2N = {2*n_at_mu(d,D,5):.3g} |')
