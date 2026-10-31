#!/usr/bin/env python3
"""meta_export.py m k r OUT [EXT]: GAP-free export (same .ht format as export_sd.g) of the metacyclic group
G = C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r> (r^k = 1 mod m), for sdtabu / sdk.

Elements x^i y^j = (i, j) have index i*k + j (identity 0), product (i,j)(a,b) = (i + r^j a, j + b), as in
records/build_metacyclic_haar.py.  Automorphisms: only the formula family beta = (a, b, c): x -> x^a, y -> x^b y^c
(a unit mod m, c unit mod k, r^c = r mod m, b * sigma_c(k) = 0 mod m with sigma_c(j) = sum_{t<j} r^(c t)); then
beta(x^i y^j) = (a i + b sigma_c(j), c j).  Records written:
  ALPHA 1  beta = identity;
  ALPHA 2  one involution of the family per conjugacy class under the family (which contains Inn(G));
  EXT c    (with the EXT argument, for even valency): pairs (beta, c), beta in the family, c <> e, beta(c) = c,
           beta^2 = conjugation x -> c x c^-1, one per class under the family.
CENT lists are empty (sdtabu ignores them; for sdk this only switches off the first-orbit normalisation).
Automorphisms outside the family (when <x> is not characteristic) are missed: the search is then less complete,
never wrong.
"""
import sys
from math import gcd
import numpy as np


def main():
    m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) % int(sys.argv[1])
    out = sys.argv[4]
    want_ext = len(sys.argv) > 5 and sys.argv[5].upper() == "EXT"
    assert pow(r, k, m) == 1 % m, "need r^k = 1 mod m"
    n = m * k
    rp = [pow(r, j, m) for j in range(k)]
    I = np.arange(n) // k
    J = np.arange(n) % k
    rpJ = np.array(rp, dtype=np.int64)[J]
    tab = ((I[:, None] + rpJ[:, None] * I[None, :]) % m) * k + (J[:, None] + J[None, :]) % k
    rinv = pow(r, -1, m) if gcd(r, m) == 1 else None
    inv = np.empty(n, dtype=np.int64)
    for e in range(n):
        i, j = divmod(e, k)
        jj = (-j) % k
        inv[e] = ((-rp[jj] * i) % m) * k + jj          # (i,j)^-1 = (-r^-j i, -j) and r^-j = r^(k-j)
    assert (tab[np.arange(n), inv] == 0).all()
    ninv = int(((tab[np.arange(n), np.arange(n)] == 0).sum()) - 1)

    def sig(c, j):            # sum_{t<j} r^(c t) mod m
        q = pow(r, c, m); s = 0; p = 1
        for _ in range(j):
            s = (s + p) % m; p = p * q % m
        return s

    sigtab = {}

    def sigma(c, j):
        key = (c, j)
        if key not in sigtab:
            sigtab[key] = sig(c, j)
        return sigtab[key]

    units_k = [c for c in range(1, k + 1) if gcd(c, k) == 1 and pow(r, c, m) == r % m]
    units_k = [c % k if k > 1 else 0 for c in units_k]

    def valid_b(c):
        s = sigma(c, k)
        step = m // gcd(s, m)
        return list(range(0, m, step))

    def comp(g, h):           # g o h
        a1, b1, c1 = g; a2, b2, c2 = h
        return (a1 * a2 % m, (a1 * b2 + b1 * sigma(c1, c2)) % m, c1 * c2 % k if k > 1 else 0)

    def finv(g):
        a, b, c = g
        ai = pow(a, -1, m); ci = pow(c, -1, k) if k > 1 else 0
        return (ai, (-ai * b * sigma(c, ci)) % m, ci)

    def apply(g, e):          # g(x^i y^j)
        a, b, c = g; i, j = divmod(e, k)
        return ((a * i + b * sigma(c, j)) % m) * k + (c * j) % k

    def perm(g):
        a, b, c = g
        sj = np.array([sigma(c, j) for j in range(k)], dtype=np.int64)
        return ((a * I + b * sj[J]) % m) * k + (c * J) % k

    # generators of the family F
    units_m = [u for u in range(1, m) if gcd(u, m) == 1] or [1]
    rng = np.random.default_rng(1)
    gens = [(int(u), 0, 1 % k) for u in rng.choice(units_m, size=min(12, len(units_m)), replace=False)]
    gens += [(1, b, 1 % k) for b in valid_b(1)[1:2]]
    gens += [(1, 0, c) for c in units_k if c != 1 % k][:12]
    gens += [(r, 0, 1 % k), (1, (1 - r) % m, 1 % k)]          # Inn(G): conjugation by y and by x
    gens = [g for g in gens if g != (1, 0, 1 % k)]
    ginv = [finv(g) for g in gens]
    for g, gi in zip(gens, ginv):
        assert comp(g, gi) == (1, 0, 1 % k)

    # involutions of the family
    invols = set()
    for a in range(1, m + (m == 1)):
        if gcd(a, m) != 1 or (a * a - 1) % m:
            continue
        for c in units_k:
            if (c * c - 1) % k:
                continue
            for b in valid_b(c):
                g = (a % m, b, c)
                if g == (1 % m, 0, 1 % k):
                    continue
                if comp(g, g) == (1 % m, 0, 1 % k):
                    invols.add(g)
    reps = []
    seen = set()
    for g in sorted(invols):
        if g in seen:
            continue
        reps.append(g); orb = [g]; seen.add(g)
        while orb:
            h = orb.pop()
            for s, si in zip(gens, ginv):
                h2 = comp(comp(s, h), si)
                if h2 not in seen:
                    seen.add(h2); orb.append(h2)
    ext = []
    if want_ext:
        rpow = {}
        for j in range(k):
            rpow.setdefault(rp[j], []).append(j)
        one_r = (1 - r) % m
        pairs = set()
        for a in range(1, m + (m == 1)):
            if gcd(a, m) != 1 or (a * a) % m not in rpow:
                continue
            js = rpow[(a * a) % m]
            for c in units_k:
                if (c * c - 1) % k:
                    continue
                for b in valid_b(c):
                    g = (a % m, b, c)
                    b2 = comp(g, g)[1]
                    gg = gcd(one_r, m)
                    if b2 % gg:
                        continue
                    mg = m // gg
                    i0 = (b2 // gg) * pow(one_r // gg, -1, mg) % mg if mg > 1 else 0
                    for i in range(i0, m, mg):
                        for j in js:
                            e = i * k + j
                            if e != 0 and apply(g, e) == e:
                                pairs.add((g, e))
        seenp = set()
        for p in sorted(pairs):
            if p in seenp:
                continue
            ext.append(p); orb = [p]; seenp.add(p)
            while orb:
                g, e = orb.pop()
                for s, si in zip(gens, ginv):
                    p2 = (comp(comp(s, g), si), apply(s, e))
                    if p2 not in seenp:
                        seenp.add(p2); orb.append(p2)
    with open(out, "w") as f:
        f.write(f"{n} {ninv}\n")
        for row in tab:
            f.write(" ".join(map(str, row.tolist())) + "\n")
        f.write(" ".join(map(str, inv.tolist())) + "\n")
        f.write("ALPHA 1\n" + " ".join(map(str, range(n))) + "\nCENT 0\n")
        for g in reps:
            p = perm(g)
            assert (p[p] == np.arange(n)).all()
            f.write("ALPHA 2\n" + " ".join(map(str, p.tolist())) + "\nCENT 0\n")
        for g, e in ext:
            f.write(f"EXT {e}\n" + " ".join(map(str, perm(g).tolist())) + "\nCENT 0\n")
    print(f"meta_export m {m} k {k} r {r} n {n} ninv {ninv} alpha2 {len(reps)} ext {len(ext)} "
          f"reps {' '.join(f'{a},{b},{c}' for a, b, c in reps)}", flush=True)


if __name__ == "__main__":
    main()
