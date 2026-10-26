"""Build and BFS-verify clique graphs for the planned multisets. Writes one JSON line per K."""
import json, sys, time
sys.path.insert(0, '.')
from clique import build_graph
from check import hub_check
delta = int(sys.argv[1]); plan_file = sys.argv[2]; out_file = sys.argv[3]
plan = json.load(open(plan_file))
size = {2:7,3:13,4:21,5:31}
with open(out_file, 'w') as out:
    for Ks, cnt in sorted(plan.items(), key=lambda kv: int(kv[0])):
        K = int(Ks)
        sizes = sorted([int(s) for s, c in cnt.items() for _ in range(c)], reverse=True)
        assert sum(size[s] for s in sizes) == K
        t = time.time(); rec = None
        for seed in range(6):
            G = build_graph(sizes, delta, seed=seed)
            if G is None: continue
            r = hub_check(G)
            rec = dict(K=K, sizes=sizes, seed=seed, valid=r['valid'], nA=r['nA'], nB=r['nB'], maxdeg=r['maxdeg'], n=r['n'], secs=round(time.time()-t,1))
            break
        if rec is None:
            rec = dict(K=K, sizes=sizes, seed=None, valid=0, note="search failed")
        out.write(json.dumps(rec) + "\n"); out.flush()
        print(rec, flush=True)
