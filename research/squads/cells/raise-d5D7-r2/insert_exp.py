# insert_exp.py: from the verified Haar record H(PGL(2,5) x Z13, S) (N = 1560, 3120 vertices, diameter 7), remove a
# 5-matching and add one A-vertex u (joined to the 5 freed B-endpoints) and one B-vertex v (joined to the 5 freed
# A-endpoints). The result has 3122 vertices, is 5-regular and bipartite. Count ordered pairs at distance > 7.
import sys, os, random, time
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import numpy as np
import r2sweep as R

def haar_nbrs(M, S):
    N = M.shape[0]
    nbr = np.empty((2 * N, len(S)), dtype=np.int64)
    for j, s in enumerate(S):
        nbr[:N, j] = N + M[s, :]          # A-vertex x ~ B-vertex s*x
    inv = R.inverse_table(M)
    for j, s in enumerate(S):
        nbr[N:, j] = inv[s] * 0 + M[inv[s], :]   # B-vertex y ~ A-vertex s^-1*y
    return nbr

def violations(nbr, D=7):
    """ordered pairs (x,y) with dist > D; nbr is V x d (regular). Bit-parallel reach sets by row gathers."""
    V = nbr.shape[0]
    R_ = np.eye(V, dtype=bool)
    for _ in range(D):
        Rn = R_.copy()
        for j in range(nbr.shape[1]):
            Rn |= R_[nbr[:, j]]
        R_ = Rn
    return int(V * V - R_.sum()), R_

def matching_edges(nbr, N, rng, k=5):
    """random k-matching of edges (A x, B y) with distinct endpoints."""
    edges = []; usedA = set(); usedB = set()
    while len(edges) < k:
        x = rng.randrange(N); j = rng.randrange(nbr.shape[1]); y = int(nbr[x, j]) - N
        if x in usedA or y in usedB: continue
        usedA.add(x); usedB.add(y); edges.append((x, y))
    return edges

def insert(nbr, N, edges):
    """Remove the matching edges, add u (A side, index 2N) and v (B side, index 2N+1)."""
    V = nbr.shape[0]
    rows = [list(map(int, nbr[x])) for x in range(V)]
    for x, y in edges:
        rows[x].remove(N + y); rows[N + y].remove(x)
    u = V; v = V + 1
    rows.append([N + y for _, y in edges])           # u ~ B-endpoints
    rows.append([x for x, _ in edges])               # v ~ A-endpoints
    for _, y in edges: rows[N + y].append(u)
    for x, _ in edges: rows[x].append(v)
    assert all(len(r) == 5 for r in rows)
    return np.array(rows, dtype=np.int64)

if __name__ == '__main__':
    S = [0, 858, 14, 367, 698]
    M = R.build_group(['PGL25', 'Z13']); N = M.shape[0]
    nbr = haar_nbrs(M, S)
    t0 = time.time(); v0, _ = violations(nbr); print(f"record: N={N} violations={v0} ({time.time()-t0:.1f}s)", flush=True)
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    for trial in range(int(sys.argv[2]) if len(sys.argv) > 2 else 3):
        edges = matching_edges(nbr, N, rng)
        nb2 = insert(nbr, N, edges)
        v1, _ = violations(nb2)
        print(f"trial {trial}: 3122-vertex insertion violations={v1}", flush=True)
