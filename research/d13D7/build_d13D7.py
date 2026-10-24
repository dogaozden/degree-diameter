#!/usr/bin/env python3
"""Self-contained construction of a bipartite graph of maximum degree 13 and diameter 7 (job cell-13-7, Oct 24 2026).
No imports from the repo; needs numpy.

Construction.
 * H = the split Cayley hexagon H(11): points = the 177,156 points of Q(x) = x0x4 + x1x5 + x2x6 - x3^2 = 0 in PG(6,11);
   the lines through a point x are the 12 lines through x in the plane pi_x = {y : B(x,y) = 0 and Tits' six equations
   p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31, p_ij = x_i y_j - x_j y_i}.  Its incidence graph I is
   12-regular, bipartite, diameter 6 (a generalized hexagon of order (11,11)), 354,312 vertices.
 * The table's (13,7) graph: three copies I x {0,1,2} plus the matching (p, i) ~ (sigma(p), i+1 mod 3) for a bijection
   sigma: points -> lines.  ANY bijection gives diameter 7 (1,062,936 vertices, 13-regular).
 * Surgery.  R = m pairwise opposite points, S = m pairwise opposite lines (opposite = distance 6 in I; for points
   this means B(x,y) != 0).  sigma(R_j) = S_j and sigma maps Gamma_2(R_j) (the 132 points collinear with R_j) onto
   Gamma_2(S_j) (the 132 lines meeting S_j), in sorted order; the remaining points go to the remaining lines in sorted
   order.  For each j the three matching edges at (R_j, i) are deleted; a new vertex v_j is joined to (R_j, 0),
   (R_j, 1), (R_j, 2) and a new vertex u_j to (S_j, 0), (S_j, 1), (S_j, 2).  v_j ~ u_k for k - j in a set C of 10
   residues mod m (so v-v and u-u pairs are close).  Max degree 13, order 1,062,936 + 2m.
 * R: the points listed in R_FILE (coordinates); S: the first m lines, in canonical order, of the Hermitian spread
   {lines of H inside n^perp}, n = (1,0,0,0,1,0,0) (1332 pairwise opposite lines).
Canonical orders: points by code sum x_i 11^i (first nonzero coordinate 1); lines by their sorted tuple of point
indices.  Vertex numbering: copy i point p -> 2N i + p, copy i line l -> 2N i + N + l (N = 177,156); v_j -> 6N + j,
u_j -> 6N + m + j.
usage: python3 build_d13D7.py R_FILE out.edges   (apsp.c format: first line n, then one edge "u v" per line)
R_FILE: one point per line as 7 coordinates "x0 x1 ... x6" ('#' lines ignored)."""
import sys
import numpy as np

q = 11
EQS = [(1, 2, 3, 4), (5, 4, 3, 2), (2, 0, 3, 5), (6, 5, 3, 0), (0, 1, 3, 6), (4, 6, 3, 1)]
C_OFFSETS = [0, 1, 3, 7, 15, 26, 40, 56, 77, 101]


def points():
    """All projective points of Q(6,q) with first nonzero coordinate 1, sorted by code."""
    out = []
    for lead in range(7):
        k = 6 - lead
        tail = np.array(np.meshgrid(*[np.arange(q)] * k, indexing='ij')).reshape(k, -1).T if k else np.zeros((1, 0), int)
        V = np.zeros((len(tail), 7), dtype=np.int64)
        V[:, lead] = 1
        V[:, lead + 1:] = tail
        Qv = (V[:, 0] * V[:, 4] + V[:, 1] * V[:, 5] + V[:, 2] * V[:, 6] - V[:, 3] ** 2) % q
        out.append(V[Qv == 0])
    P = np.concatenate(out)
    code = P @ (q ** np.arange(7))
    order = np.argsort(code)
    return P[order], code[order]


def nullspace(M):
    """Basis of {y : M y = 0} over F_q (M a list of rows)."""
    M = [row[:] for row in M]
    piv, r = [], 0
    for c in range(7):
        s = next((i for i in range(r, len(M)) if M[i][c] % q), None)
        if s is None:
            continue
        M[r], M[s] = M[s], M[r]
        inv = pow(M[r][c], q - 2, q)
        M[r] = [(a * inv) % q for a in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % q:
                f = M[i][c]
                M[i] = [(a - f * b) % q for a, b in zip(M[i], M[r])]
        piv.append(c)
        r += 1
    basis = []
    for fc in range(7):
        if fc in piv:
            continue
        v = [0] * 7
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-M[i][fc]) % q
        basis.append(v)
    return basis


def normalise(v):
    for a in v:
        if a % q:
            inv = pow(a, q - 2, q)
            return tuple((b * inv) % q for b in v)
    raise ValueError('zero vector')


def hexagon():
    P, code = points()
    N = len(P)
    assert N == (q ** 6 - 1) // (q - 1)
    index = {int(c): i for i, c in enumerate(code)}
    W = q ** np.arange(7)

    def idx(v):
        return index[int(np.dot(normalise(v), W))]

    lines = set()
    for i in range(N):
        x = [int(a) for a in P[i]]
        M = [[x[4], x[5], x[6], (-2 * x[3]) % q, x[0], x[1], x[2]]]
        for a, b, c, d in EQS:
            row = [0] * 7
            row[b] += x[a]; row[a] -= x[b]; row[d] -= x[c]; row[c] += x[d]
            M.append([t % q for t in row])
        B = nullspace(M)
        assert len(B) == 3
        # two basis vectors of the plane independent of x
        others = []
        for b in B:
            cand = others + [b]
            if len(nullspace([x] + cand)) == 7 - (len(cand) + 1):
                others = cand
            if len(others) == 2:
                break
        b0, b1 = others
        for t in range(q + 1):
            d = b1 if t == q else [(u + t * w) % q for u, w in zip(b0, b1)]
            pts = [idx(d)] + [idx([(xa + lam * da) % q for xa, da in zip(x, d)]) for lam in range(q)]
            lines.add(tuple(sorted(pts)))
    lines = sorted(lines)
    assert len(lines) == N and all(len(l) == q + 1 for l in lines)
    return P, np.array(lines, dtype=np.int64)


def bil(X, Y):
    return (X[..., 0] * Y[..., 4] + X[..., 4] * Y[..., 0] + X[..., 1] * Y[..., 5] + X[..., 5] * Y[..., 1]
            + X[..., 2] * Y[..., 6] + X[..., 6] * Y[..., 2] - 2 * X[..., 3] * Y[..., 3]) % q


def main():
    rfile, out = sys.argv[1], sys.argv[2]
    P, L = hexagon()
    N = len(P)
    print(f'H({q}): {N} points, {len(L)} lines', file=sys.stderr)
    PL = [[] for _ in range(N)]
    for l, pts in enumerate(L):
        for p in pts:
            PL[p].append(l)
    PL = np.array(PL, dtype=np.int64)
    assert PL.shape == (N, q + 1)
    # R from file
    W = q ** np.arange(7)
    code = P @ W
    R = []
    for s in open(rfile):
        s = s.strip()
        if not s or s.startswith('#'):
            continue
        v = normalise([int(t) % q for t in s.split()])
        k = int(np.dot(v, W))
        j = int(np.searchsorted(code, k))
        assert code[j] == k, 'R point not on the quadric'
        R.append(j)
    m = len(R)
    G = bil(P[R][:, None, :], P[R][None, :, :])
    np.fill_diagonal(G, 1)
    assert (G != 0).all(), 'R is not pairwise opposite'
    # S: Hermitian spread, first m lines
    n = np.array([1, 0, 0, 0, 1, 0, 0])
    onp = bil(P, n[None, :]) == 0
    spread = np.nonzero(onp[L].all(axis=1))[0]
    assert len(spread) == q ** 3 + 1
    S = [int(l) for l in spread[:m]]
    print(f'm = {m} surgeries', file=sys.stderr)

    def gamma2_point(p):
        return sorted({int(x) for l in PL[p] for x in L[l] if x != p})

    def gamma2_line(l):
        return sorted({int(k) for x in L[l] for k in PL[x] if k != l})

    sig = -np.ones(N, dtype=np.int64)
    used = np.zeros(N, dtype=bool)
    for j in range(m):
        a, b = gamma2_point(R[j]), gamma2_line(S[j])
        assert len(a) == len(b) == q * (q + 1)
        for x, y in [(R[j], S[j])] + list(zip(a, b)):
            assert sig[x] < 0 and not used[y], 'local duality regions overlap'
            sig[x] = y
            used[y] = True
    restP = np.nonzero(sig < 0)[0]
    restL = np.nonzero(~used)[0]
    sig[restP] = restL
    inR = np.zeros(N, dtype=bool)
    inR[R] = True

    nv = 6 * N + 2 * m
    E = []
    for i in range(3):
        base = 2 * N * i
        E.append(np.stack([base + L.ravel(), base + N + np.repeat(np.arange(N), q + 1)], axis=1))
        keep = np.nonzero(~inR)[0]
        E.append(np.stack([base + keep, 2 * N * ((i + 1) % 3) + N + sig[keep]], axis=1))
    for j in range(m):
        for i in range(3):
            E.append(np.array([[6 * N + j, 2 * N * i + R[j]], [6 * N + m + j, 2 * N * i + N + S[j]]]))
        offs = sorted({c % m for c in C_OFFSETS}) if m > 10 else list(range(m))
        for c in offs:
            E.append(np.array([[6 * N + j, 6 * N + m + (j + c) % m]]))
    E = np.concatenate(E)
    with open(out, 'w') as f:
        f.write(f'{nv}\n')
        np.savetxt(f, E, fmt='%d')
    print(f'n = {nv}, edges = {len(E)}', file=sys.stderr)


if __name__ == '__main__':
    main()
