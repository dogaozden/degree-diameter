"""Referee check of Corollary 6.19 (three levels, local duality, classical sets) from the printed recipe:
R = points of H(q) in Sigma_0 (Lemma 6.2(a)), R* = |R| lines of the Hermitian spread (Lemma 5.1 / 5.9),
sigma as in Proposition 6.17 with a random bijection f and random choices elsewhere, hub graph of Lemma 6.21.
Optional negative control: break (H3) at one point of R."""
import sys, random, itertools
from hexagon import Hex, write_edges
def PG22():
    pts = [(1,0,0),(0,1,0),(0,0,1),(1,1,0),(1,0,1),(0,1,1),(1,1,1)]
    inc = [[j for j, L in enumerate(pts) if sum(a*b for a, b in zip(p, L)) % 2 == 0] for p in pts]
    return inc  # inc[point] = lines on it
def pendant_hub_graph(K, delta, s=2):
    """Lemma 6.21 with core PG(2,2): returns (nB, nA, edges) with B-side = core points side."""
    t, u = delta - s - 1, delta - 1; n0 = 7
    assert n0 <= K <= n0 * (1 + t + t * u)
    c = -(-(K - n0) // (1 + u)); g = K - n0 - c; assert c <= n0 * t and g <= u * c
    inc = PG22()
    Bv = list(range(7)); Av = list(range(7)); edges = [(p, L) for p in range(7) for L in inc[p]]
    nB, nA = 7, 7
    # depth-1 children of points are A-coloured; of lines B-coloured
    d1_from_points = []; d1_from_lines = []
    for j in range(c):
        a = nA; nA += 1; edges.append((j // t if t else 0, a)); d1_from_points.append(a)
        b = nB; nB += 1; edges.append((b, j // t if t else 0)); d1_from_lines.append(b)
    for j in range(g):  # depth-2 below the points' family: B-coloured; below the lines' family: A-coloured
        par = d1_from_points[j // u]; b = nB; nB += 1; edges.append((b, par))
        par = d1_from_lines[j // u]; a = nA; nA += 1; edges.append((par, a))
    assert nB == K and nA == K
    return nB, nA, edges
def kappa(delta):
    best = 0
    for s in [2, 3, 4, 5, 7, 8, 9, 11, 13, 16]:
        if s + 1 <= delta: best = max(best, (s*s + s + 1) * (1 + (delta - s - 1) * delta))
    return best
def run(q, seed=0, control=False):
    random.seed(seed)
    H = Hex(q); F = H.F; M, A, S = F.mul, F.add, F.sub; E = list(F.elts()); N = H.N; pts = H.pts
    if q % 2:
        c = next(x for x in E if x and F.chi(F.neg[x]) == -1)
        inSig = lambda X: X[1] == 0 and X[5] == 0 and X[6] == F.neg[M[c][X[2]]]
        inPi = lambda X: A[X[0]][M[c][X[4]]] == 0
    else:
        dl = next(x for x in E if F.tr(x) == 1)
        inSig = lambda X: X[1] == 0 and X[5] == 0 and X[6] == A[M[dl][X[2]]][X[3]]
        inPi = lambda X: X[3] == A[X[0]][M[dl][X[4]]]
    R = [i for i in range(N) if inSig(pts[i])]
    assert len(R) == q*q + 1
    assert all(H.b(pts[i], pts[j]) != 0 for i, j in itertools.combinations(R, 2))   # Lemma 6.2(a)
    Pi = {i for i in range(N) if inPi(pts[i])}
    spread = [k for k in range(N) if all(i in Pi for i in H.lines[k])]
    assert len(spread) == q**3 + 1
    Rstar = random.sample(spread, len(R))
    f = dict(zip(R, Rstar))
    # Gamma_2 of a point: collinear points; of a line: concurrent lines
    col = lambda i: sorted({j for k in H.lines_on[i] for j in H.lines[k] if j != i})
    con = lambda k: sorted({kk for i in H.lines[k] for kk in H.lines_on[i] if kk != k})
    sigma = {}
    for x in R:
        sigma[x] = f[x]
        a, b = col(x), con(f[x]); assert len(a) == len(b) == q*(q+1)
        random.shuffle(b)
        for u_, w_ in zip(a, b): sigma[u_] = w_
    usedL = set(sigma.values()); assert len(usedL) == len(sigma)
    restP = [i for i in range(N) if i not in sigma]; restL = [k for k in range(N) if k not in usedL]
    random.shuffle(restL)
    for u_, w_ in zip(restP, restL): sigma[u_] = w_
    assert len(set(sigma.values())) == N
    if control:  # break (H3) at R[0]: swap the image of one collinear point with a far line
        x = R[0]; u_ = col(x)[0]; w_ = restP[0]
        sigma[u_], sigma[w_] = sigma[w_], sigma[u_]
    # check (H1)-(H3)
    Rs = set(R)
    H1 = all(not (set(col(x)) & Rs) for x in R)
    Rst = set(sigma[x] for x in R); H2 = all(not (set(con(sigma[x])) & Rst) for x in R)
    H3 = all({sigma[u_] for u_ in col(x)} == set(con(sigma[x])) for x in R)
    # vertices: (elt, level): points 0..N-1, lines N..2N-1 ; level j offset 2N*j
    V = lambda e, j: 2 * N * j + e
    edges = []
    for j in range(3):
        for k in range(N):
            for i in H.lines[k]: edges.append((V(i, j), V(N + k, j)))
        for a in range(N):
            if a in Rs: continue
            edges.append((V(a, j), V(N + sigma[a], (j + 1) % 3)))
    K = min(len(R), kappa(q - 1))
    hubR = R[:K]
    base = 6 * N
    Bh = {x: base + t for t, x in enumerate(hubR)}; Ah = {x: base + K + t for t, x in enumerate(hubR)}
    for x in hubR:
        for j in range(3):
            edges.append((Bh[x], V(x, j)))               # B-hub on the free A-slot (x, j)
            edges.append((Ah[x], V(N + sigma[x], j)))    # A-hub on the free B-slot (sigma(x), j)
    nB, nA, Y = pendant_hub_graph(K, q - 1)
    for (b, a) in Y: edges.append((Bh[hubR[b]], Ah[hubR[a]]))
    n = base + 2 * K
    fn = f"d7_cor619_q{q}{'_control' if control else ''}.edges"
    write_edges(fn, n, edges)
    print(f"q={q}: |R|={len(R)} pairwise opposite; spread {len(spread)} lines; (H1),(H2),(H3) = {H1},{H2},{H3}; K={K} (kappa(q-1)={kappa(q-1)});"
          f" order {n} = 6N+2K = {6*N+2*K}; written {fn}")
if __name__ == '__main__':
    for a in sys.argv[1:]:
        q = int(a.rstrip('c')); run(q, control=a.endswith('c'))
