"""Hill climbing over FREE labels (8 labels in Z_m, z0 = 0) for LPS(p) x Z_m covers.
cost = unreached within D from (I,0,A) and (I,0,B) (0 = FULL with diam <= D).  Accept moves with cost <= current.
Usage: hc.py p q m D evals seed [restarts]  -> appends to results_hc.jsonl whenever cost 0 is found; prints progress."""
import sys, json, random, time
import c5lib as L
p, q, m, D, evals, seed = map(int, sys.argv[1:7])
restarts = int(sys.argv[7]) if len(sys.argv) > 7 else 1
rng = random.Random(seed)
lp = L.Lps(p, q)
V = L.V_of(q, m)
out = open('results_hc.jsonl', 'a')
n = p + 1
best_overall = None
spent = 0
t0 = time.time()
def ev(z):
    global spent
    spent += 1
    c = L.cost(lp, q, m, z, D)
    return c[0], c
for rs in range(restarts):
    z = [0] + [rng.randrange(m) for _ in range(n - 1)]
    cur, info = ev(z)
    while spent < evals * (rs + 1) and cur > 0:
        improved = False
        i = rng.randrange(1, n)
        cand = list(z)
        # try a few values for coordinate i, take the best
        vals = [rng.randrange(m) for _ in range(12)]
        bestv = None
        for v in vals:
            if v == z[i]: continue
            cand[i] = v
            c, inf = ev(cand)
            if bestv is None or c < bestv[0]: bestv = (c, v, inf)
            cand[i] = z[i]
            if spent >= evals * (rs + 1): break
        if bestv and bestv[0] <= cur:
            z[i] = bestv[1]; cur = bestv[0]; info = bestv[2]
    if cur == 0:
        rec = dict(p=p, q=q, m=m, V=V, rule='free', labels=z, D=D, cost=0, diam=info[1], cA=info[2], cB=info[3])
        out.write(json.dumps(rec) + '\n'); out.flush()
        print('FOUND', rec, flush=True)
    if best_overall is None or cur < best_overall[0]: best_overall = (cur, z)
    print('restart', rs, 'cost', cur, 'z', z, 'spent', spent, 'secs', round(time.time() - t0), flush=True)
print('BEST', best_overall, flush=True)
