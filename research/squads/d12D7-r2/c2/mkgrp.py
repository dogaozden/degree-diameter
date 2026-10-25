#!/usr/bin/env python3
"""PGRP builder for affine groups G = V x| H, V = GF(11)^2 (order 121), H a subgroup of GL(2,11) of order 120.
Elements (u, A) with u in V, A in H; product (u,A)(w,B) = (u + A w, A B); order 14520.
Element index = Hidx[A] * 121 + (u[0] + 11 u[1]); identity index E0.

Modes:
  sl25   H = SL(2,5) inside SL(2,11): H = <s,t>, s of order 4, t of order 3 or 6, |<s,t>| = 120.
  singer H = F_121^* (cyclic of order 120, multiplication matrices on GF(11)^2 = GF(121)).

Generators (left multiplication): translation (e1, I) and generators of H. The order-20 subgroups are the
translation conjugates v K' v^-1 = {(v - A v, A) : A in K'} of the order-20 subgroups K' of H. Each contains a unique
involution (2v, -I) (-I is the unique involution of H); it is the designated c.
Usage: python3 mkgrp.py MODE OUT.pgrp NSUB SEED"""
import sys, random, itertools
from collections import Counter

P = 11
I2 = (1, 0, 0, 1)
NEG = (P - 1, 0, 0, P - 1)


def mmul(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return ((a * e + b * g) % P, (a * f + b * h) % P, (c * e + d * g) % P, (c * f + d * h) % P)


def mvec(A, v):
    a, b, c, d = A
    x, y = v
    return ((a * x + b * y) % P, (c * x + d * y) % P)


def morder(A):
    k, X = 1, A
    while X != I2:
        X = mmul(X, A)
        k += 1
    return k


def closure(gens, limit):
    S = {I2}
    fr = [I2]
    while fr:
        nf = []
        for x in fr:
            for g in gens:
                y = mmul(x, g)
                if y not in S:
                    S.add(y)
                    nf.append(y)
                    if len(S) > limit:
                        return None
        fr = nf
    return frozenset(S)


def vidx(v):
    return v[0] + P * v[1]


def find_H(mode):
    if mode == "sl25":
        SL = [m for m in itertools.product(range(P), repeat=4) if (m[0] * m[3] - m[1] * m[2]) % P == 1]
        o4 = [A for A in SL if morder(A) == 4]
        o36 = [A for A in SL if morder(A) in (3, 6)]
        for s in o4:
            for t in o36:
                H = closure([s, t], 200)
                if H is not None and len(H) == 120:
                    return H, [s, t]
        raise SystemExit("no SL(2,5) found")
    if mode == "singer":
        # GF(121) = GF(11)[i], i^2 = r (r a non-residue mod 11, r = 2); element a + b i <-> vector (a, b).
        r = 2
        def mulF(x, y):
            a, b = x
            c, d = y
            return ((a * c + r * b * d) % P, (a * d + b * c) % P)
        # find a generator of the cyclic group GF(121)^* (order 120)
        allF = [(a, b) for a in range(P) for b in range(P) if (a, b) != (0, 0)]
        def fpow(x, n):
            res = (1, 0)
            for _ in range(n):
                res = mulF(res, x)
            return res
        def fo(x):
            k, X = 1, x
            while X != (1, 0):
                X = mulF(X, x)
                k += 1
            return k
        w = next(x for x in allF if fo(x) == 120)
        mats = []
        for k in range(120):
            x = fpow(w, k)  # multiplication by x as a matrix acting on (a,b): columns = images of 1 and i
            c1 = mulF(x, (1, 0))
            c2 = mulF(x, (0, 1))
            mats.append((c1[0], c2[0], c1[1], c2[1]))  # row-major [[a, b],[c, d]] with columns c1, c2
        H = frozenset(mats)
        assert len(H) == 120
        return H, [mats[1]]
    raise SystemExit("mode must be sl25 or singer")


def main():
    mode, outp, nsub, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    rng = random.Random(seed)
    H, gensH = find_H(mode)
    Hl = sorted(H)
    Hidx = {A: i for i, A in enumerate(Hl)}
    cnt = Counter(morder(A) for A in Hl)
    print("H order-count", dict(sorted(cnt.items())), file=sys.stderr)
    N = 121 * len(Hl)
    E0 = Hidx[I2] * 121
    # all order-20 subgroups of H (2-generated, pairs)
    sub20 = set()
    for a in Hl:
        for b in Hl:
            K = closure([a, b], 20)
            if K is not None and len(K) == 20:
                sub20.add(K)
    print("order-20 subgroups of H:", len(sub20), file=sys.stderr)
    V = [(x, y) for y in range(P) for x in range(P)]
    def gidx(A, v):
        return Hidx[A] * 121 + vidx(v)
    allsubs = {}
    for K in sub20:
        for v in V:
            elems = []
            for A in K:
                av = mvec(A, v)
                u = ((v[0] - av[0]) % P, (v[1] - av[1]) % P)
                elems.append(gidx(A, u))
            c = gidx(NEG, ((2 * v[0]) % P, (2 * v[1]) % P))
            assert c in elems
            key = frozenset(elems)
            allsubs.setdefault(key, c)
    print("order-20 subgroups of G (translation conjugates):", len(allsubs), file=sys.stderr)
    # left-multiplication permutations
    def lmul_perm(u, C):
        perm = [0] * N
        for Bi, B in enumerate(Hl):
            CBi = Hidx[mmul(C, B)]
            for wi in range(121):
                w = (wi % P, wi // P)
                cw = mvec(C, w)
                nv = ((u[0] + cw[0]) % P, (u[1] + cw[1]) % P)
                perm[Bi * 121 + wi] = CBi * 121 + vidx(nv)
        return perm
    gens = [((1, 0), I2)] + [((0, 0), g) for g in gensH]
    perms = [lmul_perm(u, C) for (u, C) in gens]
    for p in perms:
        assert len(set(p)) == N
    keys = list(allsubs.keys())
    rng.shuffle(keys)
    keys = keys[:min(nsub, len(keys))]
    with open(outp, "w") as f:
        f.write(f"{N} {len(perms)} {E0} 20 {len(keys)}\n")
        for p in perms:
            f.write(" ".join(map(str, p)) + "\n")
        for key in keys:
            f.write(f"{allsubs[key]} " + " ".join(map(str, sorted(key))) + "\n")
    print(f"mode={mode} N={N} gens={len(perms)} subgroups written={len(keys)} -> {outp}", file=sys.stderr)


if __name__ == "__main__":
    main()
