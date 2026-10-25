#!/usr/bin/env python3
"""c1: PGRP files (clhaarP format) for groups Gamma = Z73 x|_phi K of order 14600 = 73 * 200.

K = A x|_M Z_C, A = GF(5)^k (k = 0, 1 or 2), the generator sigma of Z_C acts on A by the 5x5-matrix M (mod 5), M^C = I.
phi(a, j) = r^j mod 73 with r^C = 1. Gamma elements are (z, x), x in K, with
    (z, x)(z', x') = (z + phi(x) z', x x'),    (a, j)(b, l) = (a + M^j b, j + l) in K.
Left multiplication by g = (zg, xg):  (z, x) -> (zg + phi(xg) z, xg x).
Subgroups of order 20: H0 <= K of order 20 (joins of cyclic subgroups); its conjugate by t in Z73 is
    H(H0, t) = { ((1 - phi(x)) t, x) : x in H0 },   a complement of Z73 in Z73 x| H0 (every order-20 subgroup of Gamma
    is of this form, since gcd(20, 73) = 1).  Its designated involution c = ((1 - phi(xc)) t, xc), xc an involution of H0.

Usage: mkgrp.py NAME MODS C M R NSUB SEED [RORD REXP]
   MODS: "-" (A trivial) or "5" or "5,5";  M: k*k entries mod 5, row-major (e.g. "2,0,0,1");
   R: number of random generators;  r = r0^REXP with r0 an element of order RORD (default C) of Z73^*.
Writes NAME.pgrp and NAME.info."""
import sys, random, itertools
P = 73


def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in (2, 3)):
            return g


def elt_of_order(n):
    g = prim_root(P)
    return pow(g, (P - 1) // n, P)


def main():
    name, mods_s, C, Ms = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
    R, NSUB, SEED = int(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7])
    rord = int(sys.argv[8]) if len(sys.argv) > 8 else C
    rexp = int(sys.argv[9]) if len(sys.argv) > 9 else 1
    rng = random.Random(SEED)
    k = 0 if mods_s == "-" else len(mods_s.split(","))
    Mflat = [] if k == 0 else [int(x) % 5 for x in Ms.split(",")]
    M = [[Mflat[i * k + j] for j in range(k)] for i in range(k)]

    def mat_apply(X, a):
        return tuple(sum(X[i][j] * a[j] for j in range(k)) % 5 for i in range(k))

    def mat_mul(X, Y):
        return [[sum(X[i][t] * Y[t][j] for t in range(k)) % 5 for j in range(k)] for i in range(k)]
    I = [[int(i == j) for j in range(k)] for i in range(k)]
    Mp = [I]
    for _ in range(1, C):
        Mp.append(mat_mul(M, Mp[-1]))
    assert k == 0 or mat_mul(Mp[-1], M) == I, "M^C must be the identity"
    Aset = list(itertools.product(range(5), repeat=k))
    Kel = [(a, j) for a in Aset for j in range(C)]
    Kidx = {e: i for i, e in enumerate(Kel)}
    nK = len(Kel)
    KM = [[0] * nK for _ in range(nK)]
    for x in range(nK):
        a, j = Kel[x]
        for y in range(nK):
            b, l = Kel[y]
            ab = mat_apply(Mp[j], b) if k else ()
            KM[x][y] = Kidx[(tuple((a[i] + ab[i]) % 5 for i in range(k)), (j + l) % C)]
    kid = Kidx[(tuple([0] * k), 0)]
    r = pow(elt_of_order(rord), rexp, P)
    assert pow(r, C, P) == 1, "r^C must be 1"
    phiK = [pow(r, Kel[x][1], P) for x in range(nK)]
    for _ in range(3000):
        x, y, z = (rng.randrange(nK) for _ in range(3))
        assert KM[KM[x][y]][z] == KM[x][KM[y][z]], "K not associative"
        assert phiK[KM[x][y]] == phiK[x] * phiK[y] % P, "phi not a homomorphism"
    N = P * nK
    E0 = 0 * nK + kid

    def gel(z, x):
        return z * nK + x

    def gmul(g1, g2):
        z1, x1 = divmod(g1, nK)
        z2, x2 = divmod(g2, nK)
        return gel((z1 + phiK[x1] * z2) % P, KM[x1][x2])

    def lmul_perm(g):
        zg, xg = divmod(g, nK)
        pf = phiK[xg]
        return [gel((zg + pf * z) % P, KM[xg][x]) for z in range(P) for x in range(nK)]

    def closure(gens, limit=20):
        S = {kid}
        fr = [kid]
        while fr:
            nf = []
            for x in fr:
                for g in gens:
                    y = KM[x][g]
                    if y not in S:
                        S.add(y)
                        nf.append(y)
                        if len(S) > limit:
                            return None
            fr = nf
        return frozenset(S)
    # all subgroups of K whose order divides 20 (joins of subgroups), with generators
    subs = {}
    for x in range(nK):
        S = closure([x])
        if S is not None and S not in subs:
            subs[S] = [x]
    frontier = list(subs.keys())
    while frontier:
        new = []
        for S in frontier:
            gS = subs[S]
            if len(S) == 20:
                continue
            for x in range(nK):
                if x in S:
                    continue
                T = closure(gS + [x])
                if T is not None and 20 % len(T) == 0 and T not in subs:
                    subs[T] = gS + [x]
                    new.append(T)
        frontier = new
    H20 = [S for S in subs if len(S) == 20]
    # random generators of Gamma (left multiplication BFS reaches all of Gamma)
    while True:
        gens = [rng.randrange(N) for _ in range(R)]
        seen = {E0}
        fr = [E0]
        while fr:
            nf = []
            for x in fr:
                for g in gens:
                    y = gmul(g, x)
                    if y not in seen:
                        seen.add(y)
                        nf.append(y)
            fr = nf
        if len(seen) == N:
            break
    perms = [lmul_perm(g) for g in gens]
    cand = []
    for H in H20:
        for xc in sorted(H):
            if xc != kid and KM[xc][xc] == kid:
                cand.append((H, xc))
    rng.shuffle(cand)
    chosen, seenkey = [], set()
    tries = 0
    while len(chosen) < NSUB and tries < 200000:
        tries += 1
        H, xc = cand[rng.randrange(len(cand))]
        t = rng.randrange(P)
        key = (H, t, xc)
        if key in seenkey:
            continue
        seenkey.add(key)
        elts = [gel((1 - phiK[x]) * t % P, x) for x in H]
        c = gel((1 - phiK[xc]) * t % P, xc)
        assert gmul(c, c) == E0 and c in elts and len(set(elts)) == 20
        chosen.append((c, elts))
    with open(name + ".pgrp", "w") as f:
        f.write(f"{N} {len(gens)} {E0} 20 {len(chosen)}\n")
        for p in perms:
            f.write(" ".join(map(str, p)) + "\n")
        for c, elts in chosen:
            f.write(str(c) + " " + " ".join(map(str, elts)) + "\n")
    cnt_phi = sum(1 for H in H20 if any(phiK[x] != 1 for x in H))
    nH0 = len({H for H, xc in cand})
    info = (f"{name}: N={N} K-order={nK} C={C} mods={mods_s or '-'} M={Ms} r={r} gens={len(gens)} "
            f"order20-subgroups(K)={len(H20)} phi-nontrivial={cnt_phi} H0-with-involution={nH0} written={len(chosen)}")
    with open(name + ".info", "w") as f:
        f.write(info + "\n")
    print(info)


main()
