"""Greedy extension of the verified clique table at delta=8: for K = start..stop try multisets with few cores."""
import json, sys, time
sys.path.insert(0, '.')
from clique import build_graph
from check import hub_check
delta = 8
start, stop = int(sys.argv[1]), int(sys.argv[2])
out = open(sys.argv[3], 'a')
size = {2:7,3:13,4:21,5:31}
def cands(K):
    res = []
    for c5 in range(0, 8):
        for c4 in range(0, 12):
            for c3 in range(0, 10):
                for c2 in range(0, 13):
                    tot = c5 + c4 + c3 + c2
                    if tot < 2 or tot > 12: continue
                    if c5 * 31 + c4 * 21 + c3 * 13 + c2 * 7 != K: continue
                    res.append({5:c5,4:c4,3:c3,2:c2})
    res.sort(key=lambda c: (sum(c.values()), -c.get(5,0)))
    return res
for K in range(start, stop + 1):
    done = False
    for cnt in cands(K)[:6]:
        sizes = sorted([s for s, c in cnt.items() for _ in range(c)], reverse=True)
        for seed in range(2):
            t = time.time()
            G = build_graph(sizes, delta, seed=seed)
            if G is None: continue
            r = hub_check(G)
            if r['valid'] and r['nA'] == K and r['nB'] == K:
                rec = dict(K=K, sizes=sizes, seed=seed, valid=1, n=r['n'], maxdeg=r['maxdeg'], secs=round(time.time()-t,1))
                out.write(json.dumps(rec) + "\n"); out.flush(); print(rec, flush=True)
                done = True; break
        if done: break
    if not done:
        print({"K": K, "status": "no verified multiset among first 6 candidates"}, flush=True)
        out.write(json.dumps({"K": K, "valid": 0}) + "\n"); out.flush()
        break
