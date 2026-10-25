#!/usr/bin/env python3
"""classsize68.py: size of the class of a symmetric generating set S of SL(2,25) (ORDER2.md 3.4), by brute force.

The maps T(x) = a psi(x)^(+-1) b (a, b in G, psi in Aut(G) = PGammaL(2,25)) give isomorphic Haar graphs.  The members
of S's class that lie in the alpha-symmetric search space are the images T(S) with T normalising <alpha>; up to the
redundancy (a, b, psi) ~ (a z^-1, z b, conj(z) psi) these are: psi in PGammaL(2,25) normalising <alpha>, a and b in
Fix(alpha), and the optional inversion.  This script enumerates them and counts the distinct alpha-invariant images.
Usage: classsize68.py FILE (--frob 1 | --alpha "mat(a,b,c,d)") [--order K]
"""
import argparse, itertools
import numpy as np
from hgroups import read_solution
from twist import alpha_perm, find_conj
from classes68 import frame


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--frob", type=int, default=None)
    ap.add_argument("--alpha", default=None, help="conjugating element c of alpha = conj(c)")
    A = ap.parse_args()
    d, D, G, S = read_solution(A.file)
    Q = G.Q; F = Q.F; q = F.q; N = Q.order
    assert G.n == 1 and Q.kind == "sl"
    allg = np.arange(N)
    alpha = alpha_perm(G, frob=A.frob) if A.frob is not None else alpha_perm(G, conj=find_conj(Q, A.alpha))
    S = np.array(frame(G, S, alpha))
    k = 1; y = alpha[allg]
    while not np.array_equal(y, allg): y = alpha[y]; k += 1
    powers = [allg]
    for _ in range(k - 1): powers.append(alpha[powers[-1]])
    fix = allg[alpha == allg]
    mul = lambda a, b: Q.mul_vec(np.asarray(a), np.asarray(b))

    def frobj(x, j):
        if j == 0:
            return x
        fr = np.zeros(q, dtype=np.int64)
        for t in range(q):
            yv = 1
            for _ in range(F.p ** j): yv = int(F.mul[yv, t])
            fr[t] = yv if t else 0
        return Q.index(fr[Q.A[x]], fr[Q.B[x]], fr[Q.C[x]], fr[Q.D[x]])

    def conjM(M, x):
        m0, m1, m2, m3 = M
        det = int(F.add[F.mul[m0, m3], F.neg[F.mul[m1, m2]]]); di = int(F.inv[det])
        i0, i1, i2, i3 = [int(F.mul[di, v]) for v in (m3, F.neg[m1], F.neg[m2], m0)]
        a, b, c, dd = Q.A[x], Q.B[x], Q.C[x], Q.D[x]
        A_ = F.add[F.mul[m0, a], F.mul[m1, c]]; B_ = F.add[F.mul[m0, b], F.mul[m1, dd]]
        C_ = F.add[F.mul[m2, a], F.mul[m3, c]]; D_ = F.add[F.mul[m2, b], F.mul[m3, dd]]
        return Q.index(F.add[F.mul[A_, i0], F.mul[B_, i2]], F.add[F.mul[A_, i1], F.mul[B_, i3]],
                       F.add[F.mul[C_, i0], F.mul[D_, i2]], F.add[F.mul[C_, i1], F.mul[D_, i3]])

    # automorphisms psi = conj(M) o F^j normalising <alpha>: psi alpha psi^-1 = alpha^i, tested on a few elements
    test = np.random.default_rng(1).integers(0, N, 40)
    Ms = [m for m in itertools.product(range(q), repeat=4)
          if int(F.add[F.mul[m[0], m[3]], F.neg[F.mul[m[1], m[2]]]]) and m[0] in (0, 1) and (m[0] == 1 or m[1] == 1)]
    norm = []
    for M in Ms:
        for j in range(F.k):
            img = conjM(M, frobj(test, j))
            lhs = conjM(M, frobj(alpha[test], j))           # psi(alpha(x))
            if any(np.array_equal(lhs, powers[i][img]) for i in range(1, k)):
                norm.append((M, j))
    images = set()
    sym = lambda X: set(alpha[X].tolist()) == set(X.tolist())
    for M, j in norm:
        X = conjM(M, frobj(S, j))
        for X2 in (X, Q.inv_vec(X)):
            for h in fix:
                hX = mul(np.full(d, h), X2)
                for h2 in fix:
                    Y = mul(hX, np.full(d, h2))
                    if sym(Y):
                        images.add(tuple(sorted(Y.tolist())))
    print(f"{A.file.split('/')[-1]}: order {k}, |Fix| = {len(fix)}, automorphisms normalising <alpha>: {len(norm)}, "
          f"class size in the symmetric space = {len(images)}")


if __name__ == "__main__":
    main()
