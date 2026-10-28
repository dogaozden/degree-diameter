import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c10')
from lib import *
import gqlib
rng = random.Random(1)
out = []
GQS = {}
for q in [2, 3, 4, 5, 7, 8, 9]:
    GQS[q] = gqlib.W(q)
best = {}
def consider(delta, label, n, edges, nA, nB, K):
    res = check(n, edges)
    ok = res.get('valid') == 1 and res.get('nA') == nA and res.get('nB') == nB
    out.append(dict(delta=delta, family=label, KA=nA, KB=nB, maxdeg=res.get('maxdeg'), valid=bool(ok), bad=res.get('bad')))
    print(delta, label, nA, nB, res, flush=True)
    if ok and nA == nB and (delta not in best or nA > best[delta][0]):
        best[delta] = (nA, label, n, edges)

for delta in range(2, 13):
    # complete bipartite K_{d,d} (d<=delta) and C_10 for delta=2
    d = delta
    edges = [(a, d + b) for a in range(d) for b in range(d)]
    consider(delta, f"K_{{{d},{d}}}", 2 * d, edges, d, d, d)
    if delta >= 2:
        edges = [(i, (i + 1) % 10) for i in range(10)]
        consider(delta, "C10", 10, edges, 5, 5, 5)
    for p in [2, 3, 5, 7, 11]:
        if p + 1 <= delta:
            n, e, N, _ = pg2_incidence(p)
            consider(delta, f"PG(2,{p}) incidence", n, e, N, N, N)
        if p + 2 <= delta:
            n, e, N, _ = pg2_incidence(p, pendants=True)
            consider(delta, f"PG(2,{p}) incidence + pendants", n, e, 2 * N, 2 * N, 2 * N)
    for q, G in GQS.items():
        if q + 1 <= delta:
            N = G.np
            n, e = gq_incidence(G)
            consider(delta, f"GQ W({q}) incidence", n, e, N, N, N)
        r = delta - q - 1
        if r >= 1:
            L = 2 * r + 1
            N = G.np
            n, e, nA, nB = level_graph(G, r, rng)
            consider(delta, f"level graph W({q}), r={r} ({L} copies)", n, e, nA, nB, nA)
    if delta in best:
        print("BEST", delta, best[delta][0], best[delta][1], flush=True)
json.dump(out, open('/home/user/degree-diameter/research/squads/gqd5-r1/c10/explicit_results.json', 'w'), indent=1)
json.dump({str(d): [v[0], v[1]] for d, v in best.items()}, open('/home/user/degree-diameter/research/squads/gqd5-r1/c10/explicit_best.json', 'w'), indent=1)
