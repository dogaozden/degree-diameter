"""Referee check of Section 5.5 (even q) and Appendix B (q=2), from the printed formulas."""
import sys, itertools
from collections import deque
from hexagon import Hex, write_edges
APPB = """(0010000) (0000110) (1010000) (0000010) (0110000) (0000111) (1110000) (0000011)
(0010100) (0111010) (0110100) (0011011) (1011100) (0010010) (1111100) (0110011)
(1000010) (0011001) (0101010) (1010101) (1111010) (0111001) (1011110) (1110101)"""
def run(q, m=2, build=True):
    H = Hex(q); F = H.F; M, A, inv = F.mul, F.add, F.inv; E = list(F.elts()); N = H.N; pts = H.pts
    dl = next(x for x in E if F.tr(x) == 1)
    v = H.line_of((0, 1, 0, 0, 0, 0, 0), (0, 0, 0, 0, 0, 0, 1))
    inPi = lambda X, z: X[3] == A[A[A[X[0]][M[dl][X[4]]]][M[z[0]][X[2]]]][M[z[1]][X[5]]]
    Z = [(a, b) for a in E for b in E]
    Sz = {}
    for z in Z:
        P = {i for i in range(N) if inPi(pts[i], z)}
        assert len(P) == (q + 1) * (q**3 + 1)
        Sz[z] = [k for k in range(N) if all(i in P for i in H.lines[k])]
        assert len(Sz[z]) == q**3 + 1 and v in Sz[z]
        cnt = {}
        for k in Sz[z]:
            for i in H.lines[k]: cnt[i] = cnt.get(i, 0) + 1
        assert all(cnt.get(i, 0) == 1 for i in P)
    for z, w in itertools.combinations(Z, 2): assert set(Sz[z]) & set(Sz[w]) == {v}
    dist = {('L', v): 0}; dq = deque([('L', v)])
    while dq:
        u = dq.popleft()
        nb = [('P', i) for i in H.lines[u[1]]] if u[0] == 'L' else [('L', k) for k in H.lines_on[u[1]]]
        for w_ in nb:
            if w_ not in dist: dist[w_] = dist[u] + 1; dq.append(w_)
    near = {i for i in range(N) if dist[('P', i)] <= 3}
    assert near == {i for i in range(N) if pts[i][2] == 0 and pts[i][5] == 0}
    Pi = {i for i in range(N) if inPi(pts[i], (0, 0))}
    assert all(i in H.lines[v] for i in near & Pi)
    S0 = set(Sz[(0, 0)])
    free = [i for i in range(N) if i not in Pi and dist[('P', i)] == 5]
    assert len(free) == q**3 * (q*q - 1)
    def nu(X):
        num = A[A[M[X[2]][X[3]]][M[X[2]][X[4]]]][M[X[4]][X[5]]]; den = A[A[M[dl][M[X[2]][X[2]]]][M[X[2]][X[5]]]][M[X[5]][X[5]]]
        return M[num][inv[den]]
    assert all(len({nu(pts[i]) for i in H.lines[k]}) == 1 for k in S0 if k != v)
    def G(c0, c1, a, b):
        return A[M[A[M[c0][a]][M[c1][b]]][A[A[M[a][a]][M[a][b]]][M[dl][M[b][b]]]]][M[b][M[b][b]]]
    good = [(c0, c1) for c0 in E for c1 in E if all(G(c0, c1, a, b) for a in E for b in E if (a, b) != (0, 0))]
    out = f"q={q}: delta={dl}; Lemma 5.9 ok; free points {len(free)}; zero-free (c0,c1): {len(good)} pairs"
    W = None
    if good:
        c0, c1 = good[0]
        Fz = lambda z: M[G(c0, c1, *z)][inv[A[A[M[z[0]][z[0]]][M[z[0]][z[1]]]][M[dl][M[z[1]][z[1]]]]]]
        W = []
        for z in Z:
            if z == (0, 0): continue
            for k in Sz[z]:
                if k == v: continue
                X = [i for i in H.lines[k] if i in Pi]; assert len(X) == 1
                if nu(pts[X[0]]) == Fz(z): W.append(k)
        cover = {}
        for k in W:
            for i in H.lines[k]:
                if i not in Pi: cover[i] = cover.get(i, 0) + 1
        exact = all(cover.get(i, 0) == 1 for i in free)
        out += f"; with (c0,c1)={good[0]}: |W|={len(W)}, exact {exact}"
        # key identity, char 2
        bad = 0
        for i in free:
            p = list(pts[i]); lam = A[A[p[0]][p[3]]][M[dl][p[4]]]; il = inv[lam]; p = [M[il][t] for t in p]
            p2, p3, p4, p5 = p[2], p[3], p[4], p[5]
            Th = A[A[M[dl][M[p2][p2]]][M[p2][p5]]][M[p5][p5]]
            for z in Z:
                al, be = z
                if A[M[al][p2]][M[be][p5]] != 1: continue
                k = next(kk for kk in H.lines_on[i] if kk in set(Sz[z]))
                X = [pts[j] for j in H.lines[k] if j in Pi][0]
                lhs = A[nu(X)][M[M[be][M[be][be]]][inv[A[A[M[al][al]][M[al][be]]][M[dl][M[be][be]]]]]]
                rhs = M[A[A[A[M[p2][p3]][M[p2][p4]]][M[p4][p5]]][M[be][M[p2][p2]]]][inv[Th]]
                bad += lhs != rhs
        out += f"; Lemma 5.12 failures {bad}"
    if q == 2:
        toks = APPB.split()
        vecs = [tuple(int(ch) for ch in t.strip('()')) for t in toks]
        W = [H.line_of(vecs[2*j], vecs[2*j + 1]) for j in range(12)]
        assert all(dist[('L', k)] == 6 and k not in S0 for k in W)
        cover = {}
        for k in W:
            for i in H.lines[k]:
                if i not in Pi: cover[i] = cover.get(i, 0) + 1
        out += f"; Appendix B: 12 lines of H(2), opposite v, not in S; exact: {all(cover.get(i,0)==1 for i in free) and len(cover)==len(free)}"
    print(out)
    if W is not None and build:
        Wset = set(W); Pv = set(H.lines[v]); Lv = {k for i in Pv for k in H.lines_on[i] if k != v}
        lvl = {('P', i): (1 if i in Pv else (0 if i in Pi else -1)) for i in range(N)}
        for k in range(N): lvl[('L', k)] = 2 if k == v else (1 if k in S0 else (0 if (k in Lv or k in Wset) else -1))
        ver = {}
        for x, l in lvl.items():
            for w in itertools.product(range(m), repeat=l + 1): ver[(x, w)] = len(ver)
        edges = []
        for k in range(N):
            for i in H.lines[k]:
                for wl in itertools.product(range(m), repeat=lvl[('L', k)] + 1):
                    for wp in itertools.product(range(m), repeat=lvl[('P', i)] + 1):
                        s_ = min(len(wl), len(wp))
                        if wl[:s_] == wp[:s_]: edges.append((ver[(('P', i), wp)], ver[(('L', k), wl)]))
        write_edges(f"d6even_q{q}_m{m}.edges", len(ver), edges)
        print(f"   doubling m={m}: {len(ver)} vertices; formula {2*(q+1)*(q**4+q*q+1)+(m-1)*(2*q**4+2*q**3+2*q+2+m*(q**3+q+2)+m*m)}")
for q in map(int, sys.argv[1:]): run(q)
