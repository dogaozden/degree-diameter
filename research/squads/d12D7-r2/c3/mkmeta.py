"""PGRP writer for metacyclic groups G = Z_n x|_r Z_m: (x1,y1)(x2,y2) = (x1 + r^y1 x2 mod n, y1 + y2 mod m),
requires r^m = 1 mod n and gcd(r,n)=1. Element index = y*n + x (identity 0). Generators a=(1,0), b=(0,1).
Subgroups of order h=20: closures of random pairs/singletons of order exactly 20, each with an involution c.
Usage: mkmeta.py n m r NSUB seed OUT.pgrp"""
import sys, random
from math import gcd

def main():
    n, m, r, nsub, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
    assert gcd(r, n) == 1 and pow(r, m, n) == 1 % n, "need r^m = 1 mod n"
    N = n * m
    rp = [pow(r, y, n) for y in range(m)]
    def mul(g, h):
        xg, yg = g % n, g // n
        xh, yh = h % n, h // n
        return ((yg + yh) % m) * n + (xg + rp[yg] * xh) % n
    E = 0
    A = 1            # (1,0)
    B = 1 * 0 + n    # (0,1)
    perms = [[mul(A, y) for y in range(N)], [mul(B, y) for y in range(N)]]
    rng = random.Random(seed)
    subs = {}
    def closure(gens, bound=20):
        S = {E}; fr = [E]
        while fr:
            nf = []
            for x in fr:
                for g in gens:
                    z = mul(x, g)
                    if z not in S:
                        S.add(z); nf.append(z)
                        if len(S) > bound: return None
            fr = nf
        return S
    tries = 0
    while len(subs) < 6 * nsub and tries < 400000:
        tries += 1
        g = rng.randrange(N)
        h = rng.randrange(N) if rng.random() < 0.6 else None
        S = closure([g] if h is None else [g, h])
        if S is not None and len(S) == 20:
            subs.setdefault(frozenset(S), True)
    cands = []
    for S in subs:
        invs = [x for x in S if x != E and mul(x, x) == E]
        if invs: cands.append((invs[0], sorted(S)))
    rng.shuffle(cands)
    cands = cands[:nsub]
    with open(out, 'w') as f:
        f.write(f"{N} 2 {E} 20 {len(cands)}\n")
        for pm in perms: f.write(" ".join(map(str, pm)) + "\n")
        for c, S in cands: f.write(f"{c} " + " ".join(map(str, S)) + "\n")
    print(f"N={N} n={n} m={m} r={r} order(r)={next(k for k in range(1,m+1) if pow(r,k,n)==1)} "
          f"subgroups={len(cands)} (found {len(subs)} distinct) -> {out}")

main()
