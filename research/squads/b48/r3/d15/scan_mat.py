import sys, time, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/r3/d15')
import numpy as np
from grp_mat import make_group
from coset import subgroups4, build_nbr, cost_of, write_edges
kind, q, samples, tlimit, seed, tag = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
t0 = time.time()
N, mul = make_group(kind, q)
subs = subgroups4(N, mul)
print(f"{kind}({q}) order {N}, n={N//2}, order-4 subgroups {len(subs)}", flush=True)
sets = [set(s) for s in subs]
rng = random.Random(seed)
best = None; res = []
tries = 0; done = 0
while done < samples and time.time() - t0 < tlimit:
    tries += 1
    a = rng.randrange(len(subs)); b = rng.randrange(len(subs))
    if a == b or (sets[a] & sets[b]) != {0}: continue
    nbr, idH, idK, NL = build_nbr(N, mul, subs[a], subs[b])
    c = cost_of(nbr, NL)
    done += 1
    res.append((c, subs[a], subs[b]))
    if best is None or c < best[0]:
        best = (c, subs[a], subs[b])
        print(f"best cost={c} H={subs[a]} K={subs[b]} t={time.time()-t0:.1f}s", flush=True)
        if c == 0:
            write_edges(f"/home/user/degree-diameter/research/squads/b48/r3/d15/{tag}_valid.edges", nbr, NL)
res.sort()
print(f"evals={done} time={time.time()-t0:.1f}s", flush=True)
for r in res[:3]: print("top", r)
import collections
print("cost histogram (min 10 values):", sorted(c for c,_,_ in res)[:10], "median", sorted(c for c,_,_ in res)[len(res)//2] if res else None)
