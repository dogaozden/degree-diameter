"""Independent check of the q=5 clique number (no clique of size k+1 through vertex 0) with pysat."""
import sys, numpy as np
from pysat.card import CardEnc, EncType
from pysat.solvers import Cadical153
adj = np.load('adj_q5.npy')
N = adj.shape[0]
nb = np.nonzero(adj[0])[0]
n = len(nb)
def solve(k):
    # clique of size k among N(0) (plus vertex 0) -> need k-1 vertices in N(0)
    top = n
    clauses = []
    for i in range(n):
        for j in range(i + 1, n):
            if not adj[nb[i], nb[j]]:
                clauses.append([-(i + 1), -(j + 1)])
    enc = CardEnc.atleast(lits=list(range(1, n + 1)), bound=k - 1, top_id=top, encoding=EncType.seqcounter)
    with Cadical153(bootstrap_with=clauses + enc.clauses) as s:
        ok = s.solve()
        model = s.get_model() if ok else None
    return ok, ([nb[i] for i in range(n) if model[i] > 0] if ok else None)
for k in [7, 8]:
    ok, cl = solve(k)
    print('clique of size', k, 'containing vertex 0 exists:', ok, cl if ok else '')
    if ok:
        assert all(adj[a, b] for a in cl for b in cl if a != b)
        print('  verified pairwise adjacent')
