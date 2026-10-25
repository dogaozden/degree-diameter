# weighted max independent set on sigma-super-row conflict graphs by simulated annealing (small graphs)
import numpy as np, sys, pickle, random, math, time
from collections import defaultdict
kind, iters, seed = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
random.seed(seed)
supers = pickle.load(open(f'super_{kind}.pkl', 'rb'))
meta = pickle.load(open('hexact_meta.pkl', 'rb'))
orbs = meta['orbs_l'] if kind == 'sp' else meta['orbs_p']
# weight in g-orbit units: sum over members of |h-orbit|/61
W = []
for orb, cols in supers:
    W.append(sum(len(orbs[r]) for r in orb) // 61)
n = len(supers)
colsets = [set(c) for _, c in supers]
bycol = defaultdict(list)
for i, cs in enumerate(colsets):
    for c in cs: bycol[c].append(i)
nb = [set() for _ in range(n)]
for c, lst in bycol.items():
    for a in lst:
        for b in lst:
            if a != b: nb[a].add(b)
nb = [list(s) for s in nb]
print(kind, 'super-rows', n, 'weights', {w: W.count(w) for w in set(W)}, flush=True)
best_w = -1; best_S = None
t0 = time.time()
def run(T0, T1, steps):
    S = set(); inS = [False]*n; w = 0
    cur = 0; bw = 0; bS = set()
    for it in range(steps):
        T = T0 * (T1 / T0) ** (it / steps)
        v = random.randrange(n)
        if inS[v]:
            if random.random() < 0.5:
                # remove v
                if random.random() < math.exp(-W[v] / max(T, 1e-9)):
                    inS[v] = False; S.discard(v); cur -= W[v]
            continue
        conf = [u for u in nb[v] if inS[u]]
        delta = W[v] - sum(W[u] for u in conf)
        if delta >= 0 or random.random() < math.exp(delta / max(T, 1e-9)):
            for u in conf:
                inS[u] = False; S.discard(u); cur -= W[u]
            inS[v] = True; S.add(v); cur += W[v]
            if cur > bw:
                bw = cur; bS = set(S)
    return bw, bS
restarts = 0
while time.time() - t0 < float(sys.argv[4]) if len(sys.argv) > 4 else 20:
    bw, bS = run(3.0, 0.05, iters)
    restarts += 1
    if bw > best_w:
        best_w, best_S = bw, bS
        print('restart', restarts, 'best weight (g-orbits)', best_w, 'super-rows', len(best_S), flush=True)
pickle.dump(sorted(best_S), open(f'wsa_{kind}_{seed}.pkl', 'wb'))
print('final', kind, best_w)
