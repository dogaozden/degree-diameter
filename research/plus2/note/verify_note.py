"""Run from the repo root: python research/plus2/note/verify_note.py
Third independent build of the four-hat construction, written from the note's rules (Section 2).
Checks: order, max degree, bipartite (by construction), diameter <= 3; plus the two negative controls."""
import itertools, random, sys
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else "problems/bipartite_dd")
import lib

def plane(q):
    n, edges = lib.projective_plane_incidence(q)
    N = n // 2
    L = [set() for _ in range(N)]
    for p, l in edges: L[l - N].add(p)
    return N, L

def build(N, L, ell, A, P, X0, X1, Xa, Xc, rotate=True, link=True):
    pts_on = {j: set(L[j]) for j in range(N)}            # line -> points (Pi)
    line = lambda x, y: next(j for j in range(N) if x in L[j] and y in L[j])
    AX = {x: line(A, x) for x in L[ell]}
    X = {'0': X0, '1': X1, 'a': Xa, 'c': Xc}
    # vertices: points 0..N-1, Q, H0,H1,Ha,Hc ; lines 0..N-1, M, K0,K1,Ka,Kc
    Q, H = 'Q', {s: 'H' + s for s in X}
    M, K = 'M', {s: 'K' + s for s in X}
    inc = {(p, j) for j in range(N) for p in L[j]}
    for s in X: inc.discard((X[s], AX[X[s]]))
    if rotate: inc |= {(X1, AX[X0]), (Xc, AX[X1]), (X0, AX[Xc])}
    star = L[ell] - {X0, X1, Xc}
    for s in X:
        inc |= {(H[s], j) for j in range(N) if X[s] in L[j] and j != ell}
        inc |= {(p, K[s]) for p in L[AX[X[s]]] if p != A}
    inc |= {(x, M) for x in star} | {(H[s], M) for s in X}
    inc |= {(Q, AX[x]) for x in star} | {(Q, K[s]) for s in X}
    inc |= {(A, K['a']), (H['a'], ell), (H['0'], K['c']), (H['c'], K['1'])}
    if link: inc.add((H['1'], K['0']))
    return inc

def check(inc, d):
    P = {('p', a) for a, _ in inc}; Ls = {('l', b) for _, b in inc}
    adj = {}
    for a, b in inc:
        adj.setdefault(('p', a), set()).add(('l', b)); adj.setdefault(('l', b), set()).add(('p', a))
    n = len(adj)
    maxdeg = max(len(v) for v in adj.values())
    # diameter <= 3 for bipartite: every two points share a line, every two lines share a point, and no isolated vertex
    ok = all(adj[u] & adj[v] for side in (P, Ls) for u, v in itertools.combinations(side, 2))
    return n, maxdeg, ok

for q in [4, 5, 7, 8, 9, 11, 13]:
    N, L = plane(q); rng = random.Random(1000 + q); res = set()
    frames = 12 if q <= 9 else 4
    for t in range(frames):
        ell = rng.randrange(N); A = rng.choice([p for p in range(N) if p not in L[ell]])
        on = list(L[ell]); rng.shuffle(on); P, X0, X1, Xa, Xc = on[:5]
        n, md, ok = check(build(N, L, ell, A, P, X0, X1, Xa, Xc), q + 2)
        res.add((n == 2 * (q*q + q + 6), md <= q + 2, ok))
    # negative controls on one frame
    ell = 0; A = min(set(range(N)) - L[0]); on = sorted(L[0]); P, X0, X1, Xa, Xc = on[:5]
    nr = check(build(N, L, ell, A, P, X0, X1, Xa, Xc, rotate=False), q + 2)[2]
    nl = check(build(N, L, ell, A, P, X0, X1, Xa, Xc, link=False), q + 2)[2]
    print(f"q={q:2d} order 2(q^2+q+6)={2*(q*q+q+6):4d}  frames={frames}  (order ok, degree ok, diameter<=3) -> {sorted(res)}   no-rotation valid={nr}  no H1-K0 valid={nl}", flush=True)
