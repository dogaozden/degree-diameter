#!/usr/bin/env python3
"""rank11.py d Nmin_vertices gainmax%: SL/PSL(2,p) x Z_n groups for (d,11) with 2N above Nmin, ranked by the c13
clump model K (research/squads/raise11/r1/c13/model.py; P(cost 0 per random orbit S) ~ exp(-K))."""
import sys, math
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise11/r1/c13")
import model
d = int(sys.argv[1]); Nmin = int(sys.argv[2]) // 2; gmax = float(sys.argv[3]) / 100; nmax = int(sys.argv[4]) if len(sys.argv) > 4 else 400
def isprime(x): return x > 1 and all(x % i for i in range(2, int(x ** .5) + 1))
def has3(n):
    if n == 1: return True
    m = n; f = 2
    while f * f <= m:
        if m % f == 0:
            if f % 3 != 1: return False
            m //= f
            if m % f == 0: return False
        f += 1
    return m == 1 or m % 3 == 1
out = []
for p in range(13, 5000):
    if not isprime(p): continue
    for fam, base in (("sl", p * (p * p - 1)), ("psl", p * (p * p - 1) // 2)):
        if base > Nmin * (1 + gmax): continue
        for n in range(max(1, Nmin // base), min(nmax, int(Nmin * (1 + gmax) // base)) + 1):
            N = base * n
            if N <= Nmin or N > Nmin * (1 + gmax) or math.gcd(p, n) != 1 or (n > 1 and (n % 2 == 0 or not has3(n))): continue
            try: f = model.group_feats(d, fam, p, n)
            except Exception: continue
            K = f["K_clump"] + f.get("K_pen", 0)
            out.append((K, fam, p, n, N, f["mu"]))
out.sort()
for K, fam, p, n, N, mu in out[:int(sys.argv[5]) if len(sys.argv) > 5 else 12]:
    print(f"{fam} {p} {n}  2N={2*N}  gain={100*(N/Nmin-1):.2f}%  mu={mu:.1f}  K={K:.2f}")
