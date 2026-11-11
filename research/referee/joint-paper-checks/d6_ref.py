"""Referee check of Section 5 (odd q) from the printed text: Lemma 5.1, whisker rule of Theorem 5.5 with the
printed table of (c, c0, c1), Lemma 5.6(c), Lemma 5.7, and the doubling of Theorem 5.3 (Definition 2.5 directly)."""
import sys, itertools
from collections import deque
from hexagon import Hex, write_edges
from gf import GF
TABLE = {3: (1, (1, 2)), 5: (2, (1, 0)), 7: (1, (1, 0)), 9: ('1+i', ('i', '2i')), 11: (1, (1, 3)), 13: (2, (1, 1))}
def table_params(q):
    F = GF(q); c, (c0, c1) = TABLE[q]
    if q == 9:  # elements a+b i are encoded as a + 3b (i^2 = -1)
        enc = {'1+i': 4, 'i': 3, '2i': 6}; c, c0, c1 = enc[c], enc[c0], enc[c1]
        assert F.mul[3][3] == F.neg[1]
    return F, c, c0, c1
def check_table():
    for q in TABLE:
        F, c, c0, c1 = table_params(q); M, A, S = F.mul, F.add, F.sub
        nonsq = F.chi(F.neg[c]) == -1
        G = lambda a, b: S[M[A[M[c0][a]][M[c1][b]]][A[M[a][a]][M[c][M[b][b]]]]][M[b][M[b][b]]]
        zf = all(G(a, b) != 0 for a in F.elts() for b in F.elts() if (a, b) != (0, 0))
        print(f"table q={q}: -c non-square {nonsq}, G zero-free {zf}")
def run(q, ms=(2,)):
    H = Hex(q); F = H.F; M, A, S, inv, neg = F.mul, F.add, F.sub, F.inv, F.neg; E = list(F.elts()); N = H.N
    _, c, c0, c1 = table_params(q)
    pts = H.pts
    e1 = (0, 1, 0, 0, 0, 0, 0); e6 = (0, 0, 0, 0, 0, 0, 1)
    v = H.line_of(e1, e6)
    inPi = lambda X, z: A[A[A[X[0]][M[c][X[4]]]][M[z[0]][X[2]]]][M[z[1]][X[5]]] == 0
    Z = [(a, b) for a in E for b in E]
    Sz = {}
    for z in Z:
        P = [i for i in range(N) if inPi(pts[i], z)]
        assert len(P) == (q + 1) * (q**3 + 1)
        Pset = set(P)
        Sz[z] = [k for k in range(N) if all(i in Pset for i in H.lines[k])]
        assert len(Sz[z]) == q**3 + 1 and v in Sz[z]
        cnt = {}
        for k in Sz[z]:
            for i in H.lines[k]: cnt[i] = cnt.get(i, 0) + 1
        assert all(cnt.get(i, 0) == 1 for i in P)               # (b)
        assert all(sum(i in Pset for i in H.lines[k]) == 1 for k in range(N) if k not in set(Sz[z]))  # (c)
    # incidence BFS from v
    adjL = lambda k: H.lines[k]
    def bfs_line(k0):
        dist = {('L', k0): 0}; dq = deque([('L', k0)])
        while dq:
            u = dq.popleft()
            nb = [('P', i) for i in H.lines[u[1]]] if u[0] == 'L' else [('L', k) for k in H.lines_on[u[1]]]
            for w in nb:
                if w not in dist: dist[w] = dist[u] + 1; dq.append(w)
        return dist
    dv = bfs_line(v)
    near = {i for i in range(N) if dv[('P', i)] <= 3}
    assert near == {i for i in range(N) if pts[i][2] == 0 and pts[i][5] == 0}   # (d)
    for z in Z:
        assert all((i in near) <= (i in H.lines[v]) for i in range(N) if inPi(pts[i], z))  # (d) second part
    # opposite lines in S_z (sample z=0 fully)
    for k in Sz[(0, 0)][:5]:
        dk = bfs_line(k)
        assert all(dk[('L', kk)] == 6 for kk in Sz[(0, 0)] if kk != k)
    for z, w in itertools.combinations(Z, 2):
        assert set(Sz[z]) & set(Sz[w]) == {v}                   # (e)
    S0 = set(Sz[(0, 0)])
    Pi = {i for i in range(N) if inPi(pts[i], (0, 0))}
    free = [i for i in range(N) if i not in Pi and dv[('P', i)] == 5]
    assert len(free) == q**3 * (q*q - 1)
    # nu and F
    def nu(X):
        num = S[M[X[2]][X[3]]][M[X[4]][X[5]]]; den = A[M[c][M[X[2]][X[2]]]][M[X[5]][X[5]]]
        assert den != 0
        return M[num][inv[den]]
    def Fz(z):
        al, be = z
        G = S[M[A[M[c0][al]][M[c1][be]]][A[M[al][al]][M[c][M[be][be]]]]][M[be][M[be][be]]]
        return M[G][inv[A[M[al][al]][M[c][M[be][be]]]]]
    # nu constant on lines of S \ {v}
    assert all(len({nu(pts[i]) for i in H.lines[k]}) == 1 for k in S0 if k != v)
    W = []
    for z in Z:
        if z == (0, 0): continue
        for k in Sz[z]:
            if k == v: continue
            X = [i for i in H.lines[k] if i in Pi]; assert len(X) == 1
            if nu(pts[X[0]]) == Fz(z): W.append(k)
    assert len(set(W)) == len(W)
    Wset = set(W)
    assert all(dv[('L', k)] == 6 and k not in S0 for k in W)
    cover = {}
    for k in W:
        for i in H.lines[k]:
            if i not in Pi: cover[i] = cover.get(i, 0) + 1
    exact = all(cover.get(i, 0) == 1 for i in free) and set(cover) == set(free)
    print(f"q={q}: Lemma 5.1 (a)-(e) ok for all {len(Z)} z; free points {len(free)}; |W|={len(W)} (q^2(q^2-1)={q*q*(q*q-1)}); exact: {exact}")
    # Lemma 5.6(c) and Lemma 5.7 numerically
    def lift(xx, z):
        al, be = z
        X0 = S[S[neg[M[c][xx[3]]]][M[al][xx[1]]]][M[be][xx[4]]]
        return (X0,) + tuple(xx)
    def Jz(xx, z):
        al, be = z; x1, x2, x3, x4, x5, x6 = xx
        return (A[S[M[al][x4]][M[be][x3]]][neg[x6]], x5, S[neg[M[c][x4]]][M[be][x5]], A[x3][M[be][x2]], neg[M[c][x2]],
                A[A[A[A[M[c][x1]][M[M[al][be]][x2]]][M[al][x3]]][M[M[c][be]][x4]]][M[M[be][be]][x5]])
    bad_c = 0
    for z in Z[:6] + Z[-3:]:
        for i in range(N):
            X = pts[i]
            if not inPi(X, z): continue
            xx = X[1:]
            JX = H.norm(lift(Jz(xx, z), z))
            k = H.line_of(X, lift(Jz(xx, z), z)) if True else None
            if k not in set(Sz[z]): bad_c += 1
    bad_key = 0; two = F.from_int(2)
    for i in free:
        p = list(pts[i]); lam = A[p[0]][M[c][p[4]]]; il = inv[lam]; p = [M[il][t] for t in p]
        p2, p3, p4, p5 = p[2], p[3], p[4], p[5]
        Th = A[M[c][M[p2][p2]]][M[p5][p5]]
        for z in Z:
            al, be = z
            if A[M[al][p2]][M[be][p5]] != neg[1]: continue
            k = next(kk for kk in H.lines_on[i] if kk in set(Sz[z]))
            X = [pts[j] for j in H.lines[k] if j in Pi][0]
            lhs = A[nu(X)][M[M[be][M[be][be]]][inv[A[M[al][al]][M[c][M[be][be]]]]]]
            rhs = M[A[S[M[p2][p3]][M[p4][p5]]][M[be][M[p2][p2]]]][inv[Th]]
            bad_key += (lhs != rhs)
    print(f"   Lemma 5.6(c) failures: {bad_c}; Lemma 5.7 key identity failures over all free p and z in A_p: {bad_key}")
    # doubling (Definition 2.5) with A_2={v}, A_1={v} u P(v) u S, A_0 = A_1 u P_Pi u L_v u W
    Pv = set(H.lines[v]); Lv = {k for i in Pv for k in H.lines_on[i] if k != v}
    lvl = {}
    for i in range(N):
        lvl[('P', i)] = 1 if i in Pv else (0 if i in Pi else -1)
    for k in range(N):
        lvl[('L', k)] = 2 if k == v else (1 if k in S0 else (0 if (k in Lv or k in Wset) else -1))
    for m in ms:
        ver = {}
        for x, l in lvl.items():
            for w in itertools.product(range(m), repeat=l + 1):
                ver[(x, w)] = len(ver)
        edges = []
        for k in range(N):
            for i in H.lines[k]:
                lx, ly = lvl[('L', k)], lvl[('P', i)]
                for wl in itertools.product(range(m), repeat=lx + 1):
                    for wp in itertools.product(range(m), repeat=ly + 1):
                        s_ = min(len(wl), len(wp))
                        if wl[:s_] == wp[:s_]:
                            edges.append((ver[(('P', i), wp)], ver[(('L', k), wl)]))
        n = len(ver)
        formula = 2*(q+1)*(q**4+q*q+1) + (m-1)*(2*q**4+2*q**3+2*q+2 + m*(q**3+q+2) + m*m)
        write_edges(f"d6_q{q}_m{m}.edges", n, edges)
        print(f"   doubling m={m}: {n} vertices, Theorem 5.8 formula {formula}; written d6_q{q}_m{m}.edges")
    return H, lvl, ver if ms else None
if __name__ == '__main__':
    check_table()
    for q in map(int, sys.argv[1:]):
        run(q, ms=(2, 3) if q == 3 else (2,))
