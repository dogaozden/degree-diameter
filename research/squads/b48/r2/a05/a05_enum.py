# Diagonal split abelian-by-cyclic groups G = (F_p1 + ... + F_pt) x| Z_k, t = 2 or 3, all components of dimension 1
# (f = 1, so d | p - 1), d >= 3, component i acts by w_i^(e_i) with w_i a fixed primitive d_i-th root of F_{p_i}.
# Prints "N spec" for LO <= N <= HI; spec is the abc.py build spec. Scalar (repeated identical component) excluded.
import sys
from math import gcd, lcm
LO, HI, t = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
def isprime(n):
    return n >= 2 and all(n % q for q in range(2, int(n ** 0.5) + 1))
comps = []
for p in range(5, HI):
    if not isprime(p) or p * 3 > HI:
        continue
    for d in range(3, p):
        if (p - 1) % d == 0:
            for e in range(1, d):
                if gcd(e, d) == 1:
                    comps.append((p, d, e))
out = set()
def spec_of(cs, k):
    return f"{k} " + ",".join(f"{p}:{d}" + (f"@{e}" if e != 1 else "") for p, d, e in cs)
def rec(cs, start):
    if len(cs) == t:
        if cs[0][2] != 1:
            return
        pr = 1; L = 1
        for p, d, e in cs:
            pr *= p; L = lcm(L, d)
        for k in range(L, HI // pr + 1, L):
            if LO <= k * pr:
                out.add((k * pr, spec_of(cs, k)))
        return
    for i in range(start, len(comps)):
        p, d, e = comps[i]
        pr = 1; L = 1
        for q, dd, ee in cs + [comps[i]]:
            pr *= q; L = lcm(L, dd)
        if pr * L > HI:
            continue
        if cs and comps[i] == cs[-1]:
            continue  # identical repeated component: scalar on a sub-block, skip
        rec(cs + [comps[i]], i + 1)
rec([], 0)
for N, s in sorted(out):
    print(N, s)
