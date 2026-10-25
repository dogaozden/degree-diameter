#!/usr/bin/env python3
"""Second sound pruning for cycle types (in addition to the det test in gen_type.py).

Let lam = cycle type of R_X (points) and mu = cycle type of R_Y (lines). Both are 2-regular multigraphs on n vertices.
(1) Spectrum: NN^T = (k-1)I+J+R_X and N^T N = (k-1)I+J+R_Y are isospectral, and both R's have eigenvalue 2 on 1,
    so R_X and R_Y have the same characteristic polynomial.
(2) Digon/triangle: if points x,y have c(x,y)=3 (R_X digon), their three common lines l1,l2,l3 pairwise meet in
    x and y, so each R_Y-row of l_i is already used up by the two others, giving an R_Y triangle component. Distinct
    digons give disjoint triangles. Hence #2(lam) <= #3(mu), and symmetrically #2(mu) <= #3(lam).
Keep lam iff some mu with the same characteristic polynomial satisfies both inequalities.
usage: spec_filter.py k   -> prints the surviving types (det test AND this filter)."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_type import partitions_min2, det_test


def charpoly(parts):
    """Integer char poly (coeff list, highest degree first) of the union of cycles, digon = weight-2 double edge.
    det(xI - A(C_m)) = U_m - 2 with U_0=2, U_1=x, U_{m+1}=x U_m - U_{m-1}."""
    def mul(p, q):
        r = [0] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                r[i + j] += a * b
        return r
    total = [1]
    for m in parts:
        # U as coefficient lists, lowest degree first
        U_prev, U = [2], [0, 1]
        for _ in range(m - 1):
            nxt = [0] + U  # x*U
            for i, c in enumerate(U_prev):
                nxt[i] -= c
            U_prev, U = U, nxt
        if m == 1:
            U = U_prev
        P = U[:]
        P[0] -= 2
        total = mul(total, P)
    return tuple(total)


def count(parts, v):
    return sum(1 for m in parts if m == v)


def survives_filter(parts, cp_class):
    lam = parts
    for mu in cp_class[charpoly(lam)]:
        if count(lam, 2) <= count(mu, 3) and count(mu, 2) <= count(lam, 3):
            return True
    return False


if __name__ == '__main__':
    k = int(sys.argv[1])
    n = k * k - k - 1
    allp = list(partitions_min2(n))
    cp_class = {}
    for p in allp:
        cp_class.setdefault(charpoly(p), []).append(p)
    multi = [v for v in cp_class.values() if len(v) > 1]
    print(f'# k={k} n={n} partitions={len(allp)} distinct charpolys={len(cp_class)} '
          f'non-unique spectra={len(multi)}', file=sys.stderr)
    det_ok = spec_ok = both = 0
    for p in allp:
        d, sq = det_test(k, p)
        s = survives_filter(p, cp_class)
        det_ok += sq; spec_ok += s
        if sq and s:
            both += 1
            print(','.join(map(str, p)))
    print(f'# det pass={det_ok} spectral/digon filter pass={spec_ok} both={both}', file=sys.stderr)
