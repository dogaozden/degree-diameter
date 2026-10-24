"""Item 4: the metacyclic Haar records Z_m x|_r Z_k (lifts branch sols/haar, frontier d6D7, research/d5/sols).

For each solution: (Δ, D), m (factorised), k, r, ord_m(r) (faithful iff = k), |G^ab| = k * gcd(r-1, m),
m prime? k | p-1?, the j-parts of S (the image of S in the quotient Z_k, up to translation), and
N/(Δ-1)^(D-2) (the size-law constant of research/frontier/SIZE_LAW.md).
Question: is there a formula for (m, k, r, S) across cells?
"""
import glob, os, re, sys
from math import gcd
from sympy import factorint, isprime, n_order

HERE = os.path.dirname(os.path.abspath(__file__))


def fmt(n): return '·'.join(f'{p}^{e}' if e > 1 else str(p) for p, e in sorted(factorint(n).items())) if n > 1 else '1'


rows = []
for p in sorted(glob.glob(os.path.join(HERE, 'meta_sols', '*.txt'))):
    L = [l for l in open(p).read().split('\n') if l.strip()]
    h = L[0].split()
    d, D, m, k, r = int(h[0]), int(h[1]), int(h[3]), int(h[4]), int(h[5])
    S = [tuple(map(int, re.search(r"a=(\d+),j=(\d+)", l).groups())) for l in L[1:1 + d]]
    rows.append((d, D, m, k, r, S, os.path.basename(p)))
for p in sorted(glob.glob(os.path.join(HERE, '..', 'd5', 'sols', '*.txt'))):
    L = [l for l in open(p).read().split('\n') if l.strip()]
    h = L[0].split()
    if len(h) != 4: continue
    d, m, k, r = map(int, h)
    S = [tuple(map(int, l.split()[:2])) for l in L[1:1 + d]]
    rows.append((d, 5, m, k, r, S, 'd5/' + os.path.basename(p)))

out = ["cell | m | k | r | ord_m(r) | |G^ab| | m prime, k | m-1 | j-parts of S (mod k) | N/(Δ-1)^(D-2) | file"]
for d, D, m, k, r, S, f in sorted(rows, key=lambda x: (x[1], x[0], -x[2] * x[3])):
    o = n_order(r, m) if gcd(r, m) == 1 and m > 1 else None
    ab = k * gcd(r - 1, m)
    js = sorted(j for a, j in S)
    pr = isprime(m)
    out.append(f"({d},{D}) | {m} = {fmt(m)} | {k} = {fmt(k)} | {r} | {o} | {ab} | {pr}{', k|m-1' if pr and (m-1) % k == 0 else ''} "
               f"| {js} | {m*k/(d-1)**(D-2):.3f} | {f}")
s = '\n'.join(out)
# summary statistics
faith = sum(1 for d, D, m, k, r, S, f in rows if gcd(r, m) == 1 and n_order(r, m) == k)
prime = sum(1 for d, D, m, k, r, S, f in rows if isprime(m))
abl = [k * gcd(r - 1, m) for d, D, m, k, r, S, f in rows]
s += f"\n\n{len(rows)} solutions; faithful action (ord r = k): {faith}; m prime: {prime}; |G^ab| range {min(abl)}..{max(abl)}"
s += "\n|G^ab| / N: " + ', '.join(f"{k*gcd(r-1,m)/(m*k):.4f}" for d, D, m, k, r, S, f in rows)
open(os.path.join(HERE, 'meta_table_out.txt'), 'w').write(s)
print(s)
