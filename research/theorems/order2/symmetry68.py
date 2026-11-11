#!/usr/bin/env python3
"""symmetry68.py: the full symmetry group of a generating set S of SL(2,q) (ORDER2.md 3.4).

H(G, S) is isomorphic to H(G, T(S)) for every map T(x) = a psi(x) b with psi in Aut(G), and for T(x) = a psi(x)^-1 b
(that one swaps the two sides).  Writing a psi(x) b = (a b) (b^-1 psi(x) b), every such T is x -> a' psi'(x).
For SL(2,q), q odd >= 5, Aut = PGammaL(2,q): psi(x) = M F^j(x) M^-1 with M in GL(2,q) and F^j a field automorphism.
T(S) = S with T(s_i) = s_pi(i) forces psi'(s_i^-1 s_j) = s_pi(i)^-1 s_pi(j) (direct maps) or
psi'(s_i s_j^-1) = s_pi(i)^-1 s_pi(j) (inverse maps).  For every permutation pi and every j this is a linear system
M F^j(x) = x' M in the four entries of M; a solution with det M != 0 is a symmetry.  Prints |Stab(S)| and which
(pi, j, direct/inverse) occur.  A beta-invariant S always has beta itself (order 2); a typical one has nothing else.
Usage: symmetry68.py FILE [--frob J | --alpha "mat(a,b,c,d)"]   (to recover the symmetric frame first)
"""
import argparse, itertools
import numpy as np
from hgroups import read_solution, MatGroup
from twist import alpha_perm, find_conj
from classes68 import frame


def nullspace(F, rows):
    """null space of a matrix over GF(q) (rows: list of length-4 int lists), via the field tables."""
    A = [list(r) for r in rows]
    ncol = 4
    piv = []
    r = 0
    for c in range(ncol):
        p = next((i for i in range(r, len(A)) if A[i][c]), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        iv = int(F.inv[A[r][c]])
        A[r] = [int(F.mul[iv, x]) for x in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c]:
                t = A[i][c]
                A[i] = [int(F.add[A[i][k], F.neg[F.mul[t, A[r][k]]]]) for k in range(ncol)]
        piv.append(c)
        r += 1
    free = [c for c in range(ncol) if c not in piv]
    basis = []
    for fc in free:
        v = [0] * ncol
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = int(F.neg[A[i][fc]])
        basis.append(v)
    return basis


def eqs(F, X, Y):
    """rows of M X - Y M = 0 for 2x2 X = (x0 x1; x2 x3), Y likewise; unknowns M = (m0 m1; m2 m3)."""
    x0, x1, x2, x3 = X
    y0, y1, y2, y3 = Y
    neg = lambda a: int(F.neg[a])
    add = lambda a, b: int(F.add[a, b])
    # (M X)_{11} = m0 x0 + m1 x2 ; (Y M)_{11} = y0 m0 + y1 m2
    return [
        [add(x0, neg(y0)), x2, neg(y1), 0],
        [x1, add(x3, neg(y0)), 0, neg(y1)],
        [neg(y2), 0, add(x0, neg(y3)), x2],
        [0, neg(y2), x1, add(x3, neg(y3))],
    ]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("file")
    ap.add_argument("--frob", type=int, default=None)
    ap.add_argument("--alpha", default=None)
    ap.add_argument("--to", default=None, help="second solution file: list the maps T with T(S) = S2 instead")
    A = ap.parse_args()
    d, D, G, S = read_solution(A.file)
    Q = G.Q
    assert isinstance(Q, MatGroup) and Q.kind == "sl" and G.n == 1, "SL(2,q) x Z_1 only"
    F = Q.F
    if A.frob is not None or A.alpha is not None:
        beta = alpha_perm(G, frob=A.frob) if A.frob is not None else alpha_perm(G, conj=find_conj(Q, A.alpha))
        Sy = frame(G, S, beta)
        assert Sy is not None
        S = Sy
    S = np.array(S)
    S2 = S
    if A.to:
        _, _, G2, T2 = read_solution(A.to)
        assert G2.N == G.N
        if A.frob is not None or A.alpha is not None:
            T2 = frame(G, T2, beta)
        S2 = np.array(T2)
    inv = G.inv_perm()
    mat = lambda x: (int(Q.A[x]), int(Q.B[x]), int(Q.C[x]), int(Q.D[x]))
    def frob_entries(m, j):
        out = []
        for t in m:
            y = 1
            for _ in range(F.p ** j):
                y = int(F.mul[y, t])
            out.append(y if t else 0)
        return tuple(out)
    dif = {(i, j): mat(G.mul_vec(np.array([inv[S2[i]]]), np.array([S2[j]]))[0]) for i in range(d) for j in range(d)}
    sdif = {(i, j): mat(G.mul_vec(np.array([inv[S[i]]]), np.array([S[j]]))[0]) for i in range(d) for j in range(d)}
    adif = {(i, j): mat(G.mul_vec(np.array([S[i]]), np.array([inv[S[j]]]))[0]) for i in range(d) for j in range(d)}
    found = []
    for pi in itertools.permutations(range(d)):
        for jj in range(F.k):
            for kind, src in (("direct", sdif), ("inverse", adif)):
                rows = []
                for i in range(1, d):
                    X = frob_entries(src[(0, i)], jj)
                    Y = dif[(pi[0], pi[i])]
                    rows += eqs(F, X, Y)
                ns = nullspace(F, rows)
                if len(ns) != 1:
                    if len(ns) > 1:
                        print("warning: null space of dimension", len(ns), pi, jj, kind)
                    continue
                m = ns[0]
                det = int(F.add[F.mul[m[0], m[3]], F.neg[F.mul[m[1], m[2]]]])
                if det == 0:
                    continue
                # check all pairs, not just those from s_0
                ok = True
                for i in range(d):
                    for j in range(d):
                        if i == j:
                            continue
                        X = frob_entries(src[(i, j)], jj)
                        Y = dif[(pi[i], pi[j])]
                        r = eqs(F, X, Y)
                        for row in r:
                            v = 0
                            for c in range(4):
                                v = int(F.add[v, F.mul[row[c], m[c]]])
                            if v:
                                ok = False
                if ok:
                    found.append((pi, jj, kind))
    what = f"maps to {A.to.split('/')[-1]}" if A.to else "|Stab(S)|"
    print(f"{A.file.split('/')[-1]}: {what} = {len(found)} (maps x -> a psi(x) and x -> a psi(x)^-1 with T(S) = S2)")
    for pi, jj, kind in found:
        print(f"   pi={pi} field-aut j={jj} {kind}")


if __name__ == "__main__":
    main()
