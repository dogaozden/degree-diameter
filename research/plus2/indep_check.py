# Independent check by the main session. Run from the repo root: python research/plus2/indep_check.py OUTDIR
"""Independent rebuild of the '+2' (four-hat) construction from the six rules in the report text only.
Usage: indep.py OUTDIR  -> writes one JSON per q (first random frame) and prints check results for many frames."""
import json, random, sys
from collections import deque
sys.path.insert(0, "problems/bipartite_dd")
import lib

def plane(q):
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    lines = [set() for _ in range(m)]
    for p, l in edges: lines[l - m].add(p)
    return m, [frozenset(L) for L in lines]

def build(q, rng):
    N, L = plane(q)
    ell = rng.randrange(len(L)); A = rng.choice([p for p in range(N) if p not in L[ell]])
    onl = sorted(L[ell]); P = rng.choice(onl)
    X0, X1, Xa, Xc = rng.sample([x for x in onl if x != P], 4)
    AX = {x: next(j for j, Ln in enumerate(L) if A in Ln and x in Ln) for x in onl}
    inc = {(p, j) for j, Ln in enumerate(L) for p in Ln}                         # points 0..N-1, lines 0..N-1
    Q, H = N, {"0": N + 1, "1": N + 2, "a": N + 3, "c": N + 4}                   # new points
    M, K = N, {"0": N + 1, "1": N + 2, "a": N + 3, "c": N + 4}                   # new lines (line ids)
    X = {"0": X0, "1": X1, "a": Xa, "c": Xc}
    for s in X: inc.discard((X[s], AX[X[s]]))                                    # rule 1: remove
    inc |= {(X1, AX[X0]), (Xc, AX[X1]), (X0, AX[Xc])}                            # rule 1: rotation
    for s in X:
        inc |= {(H[s], j) for j, Ln in enumerate(L) if X[s] in Ln and j != ell}  # rule 2
        inc |= {(p, K[s]) for p in L[AX[X[s]]] if p != A}                        # rule 3
    star = [x for x in onl if x not in (X0, X1, Xc)]
    inc |= {(x, M) for x in star} | {(H[s], M) for s in H}                       # rule 4
    inc |= {(Q, AX[x]) for x in star} | {(Q, K[s]) for s in K}                   # rule 5
    inc |= {(A, K["a"]), (H["a"], ell), (H["0"], K["c"]), (H["c"], K["1"]), (H["1"], K["0"])}  # rule 6
    npts = N + 5
    edges = [(p, npts + j) for p, j in inc]
    return 2 * npts, edges

def check(n, edges, d, D):
    adj = [[] for _ in range(n)]
    for u, v in edges: adj[u].append(v); adj[v].append(u)
    if max(len(a) for a in adj) > d: return "degree"
    for s in range(n):
        dist = [-1] * n; dist[s] = 0; dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if dist[y] < 0: dist[y] = dist[x] + 1; dq.append(y)
        if min(dist) < 0 or max(dist) > D: return "diameter"
    return "ok"

out = sys.argv[1]
for q in [4, 5, 7, 8, 9, 11, 13, 16]:
    rng = random.Random(q); res = []
    trials = 30 if q <= 9 else 8 if q <= 13 else 3
    for t in range(trials):
        n, edges = build(q, rng)
        assert n == 2 * (q * q + q + 6)
        res.append(check(n, edges, q + 2, 3))
        if t == 0:
            json.dump({"case": f"d{q+2}D3", "output": [n, [list(e) for e in edges]], "value": n}, open(f"{out}/indep_q{q}.json", "w"))
    print(f"q={q:2d} n={n} frames tried={trials} results={sorted(set(res))}", flush=True)
