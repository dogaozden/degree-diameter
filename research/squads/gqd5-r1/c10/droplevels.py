import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c10')
from lib import *
import gqlib
def test(q, r, seeds=3):
    G = gqlib.W(q); N = G.np; L = 2 * r + 1; per = 2 * N
    res_all = []
    for s in range(seeds):
        n, E, nA, nB = level_graph(G, r, random.Random(s))
        for drop in range(1, L):  # drop the last `drop` levels
            keep = set(range(L - drop))
            vid = {}
            for v in range(n):
                if v // per in keep: vid[v] = len(vid)
            ee = [(vid[u], vid[v]) for u, v in E if u in vid and v in vid]
            res = check(len(vid), ee)
            res_all.append((s, L - drop, len(vid) // 2, res.get('valid'), res.get('maxdeg'), res.get('bad')))
    return res_all
for q, r in [(5, 2), (4, 3), (9, 2)]:
    out = test(q, r)
    print("q", q, "r", r, out, flush=True)
