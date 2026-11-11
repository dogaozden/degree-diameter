# a11 planner: candidate Q x Z_n cells for (D=12) Delta=6..11, ranked by the clump model
# mu = N exp(-W/N), W = sum_{odd j<=D-1} Delta (Delta-1)^(j-1); clumps mean mu/k; fixed term F = |Fix_G| exp(-lam/k)
# (|Fix_G| includes e, as in haar_sym's "fixed-point misses" line); score = -(mu/k) - F, P ~ exp(score).
import math, sys
from math import gcd
D = int(sys.argv[1]) if len(sys.argv) > 1 else 12
CUR = {6: 4683120, 7: 29919252, 8: 142047528, 9: 552892560, 10: 1856212176, 11: 5594574048}
def W(d, D=D):
    return sum(d * (d - 1) ** (j - 1) for j in range(1, D, 2))
def mu_of(N, d):
    lam = W(d) / N
    return N * math.exp(-lam), lam
def isprime(n):
    return n > 1 and all(n % p for p in range(2, int(n ** .5) + 1))
def ordmod(r, n):
    k, x = 1, r % n
    while x != 1 % n:
        x = x * r % n; k += 1
        if k > 10 * n: return None
    return k
from functools import lru_cache
@lru_cache(None)
def best_r(n, k):
    """r in Z_n^* with r^k = 1 minimising |Fix_Z| = gcd(r-1,n); returns (fixZ, r, order)"""
    best = None
    for r in range(1, n + 1) if n > 1 else [0]:
        if n > 1 and gcd(r, n) != 1: continue
        if n == 1:
            return (1, 0, 1)
        if pow(r, k, n) != 1 % n: continue
        o = ordmod(r, n)
        if o is None or k % o: continue          # order of r must divide k
        fz = gcd(r - 1, n)
        if best is None or fz < best[0]: best = (fz, r, o)
    return best
# base groups: name, order, aut order k, |Fix_Q| (fixed subgroup of the automorphism, incl. identity)
def sl(q): return q * (q * q - 1)
def psl(q): return sl(q) // 2
Qs = []
Qs.append(("SL(2,32)", sl(32), 5, sl(2), "x->x^2 (order 5)"))
Qs.append(("SL(2,128)", sl(128), 7, sl(2), "x->x^2 (order 7)"))
Qs.append(("PSL(2,243)", psl(243), 5, psl(3), "x->x^3 (order 5)"))
Qs.append(("PSL(2,2187)", psl(3**7), 7, psl(3), "x->x^3 (order 7)"))
Qs.append(("PSL(2,125)", psl(125), 3, psl(5), "x->x^5 (order 3)"))
Qs.append(("PSL(2,343)", psl(343), 3, psl(7), "x->x^7 (order 3)"))
Qs.append(("SL(2,512)", sl(512), 9, sl(2), "x->x^2 (order 9)"))
Qs.append(("SL(2,512)", sl(512), 3, sl(8), "x->x^8 (order 3, cube)"))
# conjugation by an element of order k in PSL(2,p): Fix_Q = centraliser, cyclic of order (p-1)/2 or (p+1)/2
for k in (5, 7):
    for p in range(5, 3000):
        if not isprime(p) or p == 2 or p % k not in (1, k - 1): continue
        if p % k == 1: C = (p - 1) // 2
        else: C = (p + 1) // 2
        o = psl(p)
        if o > 1.2 * CUR[11] or o < CUR[6] / 3000: continue
        Qs.append((f"PSL(2,{p}) conj", o, k, C, f"conj order {k}"))
rows = []
for d in range(6, 12):
    cur = CUR[d]
    for (name, oQ, k, fixQ, aut) in Qs:
        if d == 6 and name.endswith("conj") and False: pass
        # f in {0,1,2}, d = f + k m
        opts = [(f, (d - f) // k) for f in (0, 1, 2) if (d - f) % k == 0 and (d - f) // k >= 1]
        if not opts: continue
        lo, hi = cur / oQ, 1.10 * cur / oQ
        if hi > 3000: continue
        for n in range(max(1, math.ceil(lo)), math.floor(hi) + 1):
            N = oQ * n
            if N < cur or N > 1.10 * cur: continue
            br = best_r(n, k)
            if br is None: continue
            fz, r, o = br
            fix = fixQ * fz
            mu, lam = mu_of(N, d)
            F = fix * math.exp(-lam / k)
            score = -(mu / k) - F
            for (f, m) in opts:
                rows.append(dict(cell=f"({d},12)", Q=name, aut=aut, k=k, n=n, N=N, r=r, fz=fz, f=f, m=m,
                                 fix=fix, mu=mu, muk=mu / k, F=F, score=score, gain=100 * (N / cur - 1),
                                 cmd=f'ORBIT="{k} {m} {f}" AFROB=? ...'))
# keep best 3 per cell
import collections
by = collections.defaultdict(list)
for r_ in rows: by[r_["cell"]].append(r_)
out = []
for cell in sorted(by, key=lambda c: int(c[1:].split(",")[0])):
    lst = sorted(by[cell], key=lambda x: -x["score"])
    out.append(f"## {cell}  (current N = {CUR[int(cell[1:].split(',')[0])]:,}; candidates: {len(lst)})")
    out.append("| rank | Q | alpha | k | n | N | gain | ORBIT k m f | r, fixZ | mu | mu/k | |Fix_G| | F | log P |")
    out.append("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for i, x in enumerate(lst[:3], 1):
        out.append(f"| {i} | {x['Q']} | {x['aut']} | {x['k']} | {x['n']} | {x['N']:,} | +{x['gain']:.2f}% | {x['k']} {x['m']} {x['f']} | r={x['r']}, {x['fz']} | {x['mu']:.1f} | {x['muk']:.2f} | {x['fix']} | {x['F']:.2f} | {x['score']:.2f} |")
    if not lst: out.append("| - | no candidate in window | | | | | | | | | | | | |")
print("\n".join(out))
