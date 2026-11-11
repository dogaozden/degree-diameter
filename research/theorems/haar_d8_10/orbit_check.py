"""Check that a record's connection set is orbit-closed, from the solution file alone.

Usage: python3 orbit_check.py SOL.txt [k]

For G = Q x Z_n with Q = SL(2,p) or PSL(2,p), p prime (one factor), the program searches for an automorphism
alpha(x, z) = (g x g^-1, r z) of order k (default 3) and an element c of S such that S is closed under
beta(x) = alpha(x) * c.  c = e means S itself is alpha-closed (files with a fixed generator e, f >= 1).  A c != e is
what Lemma 3.1(ii) of HAAR_D8_10.md predicts for files that store a right translate S0 * s0^-1 of an alpha-closed S0
(the f = 0 files): then S = S0 s0^-1 is closed under x -> alpha(x) alpha(s0) s0^-1, and c = alpha(s0) s0^-1 lies in S
because e lies in S.  The program prints the orbit structure of beta on S (sizes of the cycles).

This is a check of the search structure only. It plays no role in the diameter checks.
"""
import re
import sys

import numpy as np


def parse(path):
    lines = [ln for ln in open(path).read().split("\n") if ln.strip()]
    head = lines[0].split()
    d, D, fam, p = int(head[0]), int(head[1]), head[2], int(head[3])
    assert fam in ("sl", "psl") and head[4] == "n", "only 'sl p n' / 'psl p n' headers"
    n = int(head[5])
    S = []
    for ln in lines[1:1 + d]:
        m = re.search(r"mat\((\d+),(\d+),(\d+),(\d+)\)\s*z=(\d+)", ln)
        a, b, c, dd, z = map(int, m.groups())
        S.append(((a, b, c, dd), z))
    return d, D, fam, p, n, S


def all_sl(p):
    """every element of SL(2,p) as arrays a, b, c, d"""
    out = []
    v = np.arange(p)
    inv = np.array([0] + [pow(int(x), p - 2, p) for x in range(1, p)])
    # c != 0: a, d free, b = (ad - 1)/c
    c, a, dd = (x.ravel() for x in np.meshgrid(np.arange(1, p), v, v, indexing="ij"))
    b = ((a * dd - 1) % p) * inv[c] % p
    out.append((a, b, c, dd))
    # c = 0: a != 0, d = 1/a, b free
    a, b = (x.ravel() for x in np.meshgrid(np.arange(1, p), v, indexing="ij"))
    out.append((a, b, np.zeros_like(a), inv[a]))
    return tuple(np.concatenate([o[i] for o in out]) for i in range(4))


def key(m, p, psl):
    a, b, c, d = (x % p for x in m)
    if psl:
        return min((a, b, c, d), ((-a) % p, (-b) % p, (-c) % p, (-d) % p))
    return (a, b, c, d)


def mul(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def inv(x, p):
    a, b, c, d = x
    return (d % p, (-b) % p, (-c) % p, a % p)


def main():
    path = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    d, D, fam, p, n, S = parse(path)
    psl = fam == "psl"
    Sset = {(key(m, p, psl), z % n) for m, z in S}
    assert len(Sset) == d
    rs = [r for r in range(1, n) if np.gcd(r, n) == 1 and pow(r, k, n) == 1 % n] if n > 1 else [0]
    if n == 1:
        rs = [0]
    A, B, C, Dd = all_sl(p)
    G = (A, B, C, Dd)
    found = []
    ident = (key((1, 0, 0, 1), p, psl), 0)
    x1 = next(s for s in S if (key(s[0], p, psl), s[1] % n) != ident)
    m1, z1 = x1
    for cm, cz in S:                      # candidate c in S
        cinv = inv(cm, p)
        for tm, tz in S:                  # beta(x1) = t, i.e. alpha(x1) = t c^-1
            target = mul(tm, cinv, p)
            tzz = (tz - cz) % n if n > 1 else 0
            for r in rs:
                if n > 1 and (r * z1) % n != tzz:
                    continue
                # g m1 g^-1 = +-target  <=>  g m1 = +-target g  (4 linear equations, vectorised over all g)
                ga, gb, gc, gd = G
                lm = mul((ga, gb, gc, gd), m1, p)
                for sgn in ((1, -1) if psl else (1,)):
                    tg = tuple((sgn * t) % p for t in target)
                    rm = mul(tg, (ga, gb, gc, gd), p)
                    ok = (lm[0] == rm[0]) & (lm[1] == rm[1]) & (lm[2] == rm[2]) & (lm[3] == rm[3])
                    for i in np.flatnonzero(ok):
                        g = (int(ga[i]), int(gb[i]), int(gc[i]), int(gd[i]))
                        gi = inv(g, p)

                        def beta(s):
                            m, z = s
                            am = mul(mul(g, m, p), gi, p)
                            return mul(am, cm, p), ((r * z + cz) % n if n > 1 else 0)
                        if all((key(beta(s)[0], p, psl), beta(s)[1]) in Sset for s in S):
                            # order of conjugation by g modulo the centre {+-I}
                            o, h = 1, g
                            while key(h, p, True) != key((1, 0, 0, 1), p, True):
                                h = mul(h, g, p)
                                o += 1
                            # cycle structure of beta on S
                            pos = {(key(m, p, psl), z % n): j for j, (m, z) in enumerate(S)}
                            seen, cyc = set(), []
                            for j, s in enumerate(S):
                                if j in seen:
                                    continue
                                L, cur = 0, s
                                while True:
                                    jj = pos[(key(cur[0], p, psl), cur[1] % n)]
                                    if jj in seen:
                                        break
                                    seen.add(jj)
                                    L += 1
                                    nb = beta(cur)
                                    cur = nb
                                cyc.append(L)
                            if max(cyc) == 1 or k % o or (n > 1 and pow(r, k, n) != 1 % n):
                                continue                  # alpha trivial on S, or of the wrong order
                            found.append((cm, cz, r, g, o, sorted(cyc)))
                            break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        if found:
            break
    name = path.split("/")[-1]
    if not found:
        print(f"{name}: no automorphism alpha = conj x (z -> rz) of order {k} with S closed under x -> alpha(x) c, c in S")
        return 1
    cm, cz, r, g, o, cyc = found[0]
    ce = key(cm, p, psl) == key((1, 0, 0, 1), p, psl) and cz % n == 0
    print(f"{name}: S closed under beta(x) = alpha(x)*c with alpha = conj by mat{g} (order {o} mod centre) x (z -> {r}z mod {n}), "
          f"c = {'e' if ce else 'mat' + str(cm) + ' z=' + str(cz)}; cycle sizes of beta on S: {cyc}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
