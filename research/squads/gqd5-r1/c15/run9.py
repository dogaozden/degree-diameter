import sys, pickle, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c15')
import numpy as np, networkx as nx, slots, slots2
from grid import make_grid
P = make_grid()
def G(A):
    g = nx.DiGraph(); g.add_nodes_from(range(len(A)))
    g.add_edges_from((u, v) for u in range(len(A)) for v in range(len(A)) if A[u, v])
    return g
B = pickle.load(open('buckets9.pkl', 'rb'))
reps, gs = [], []
for bk in B:
    for A in bk:
        g = G(A)
        if not any(nx.is_isomorphic(g, h) for h in gs):
            gs.append(g); reps.append(A)
print('iso classes of regular tournaments on 9 vertices found:', len(reps), flush=True)
t = time.time()
best, forms_at, OUTa, INa, tida, typa, types = slots2.search(9, reps, P)
print('search time', round(time.time() - t, 1), flush=True)
pickle.dump(dict(P=P, n=9, best=best, forms_at=forms_at, tournaments=reps, tida=tida, typa=typa, types=types),
            open('res_9.pkl', 'wb'))
