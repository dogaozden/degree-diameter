"""Grow a valid run by one freed point per level (one more B-hub and A-hub), then anneal.
Usage: python3 grow.py in.json s_new iters seed out.json"""
import sys, json, random
import numpy as np
from anneal import anneal, bad_pairs, build_adj, NP, L
d = json.load(open(sys.argv[1])); s_new = int(sys.argv[2]); iters = int(sys.argv[3]); seed = int(sys.argv[4])
out = sys.argv[5]
rng = random.Random(seed)
M = [np.array(m) for m in d['M']]
Bs = [np.array(b) for b in d['Bs']]; As = [np.array(a) for a in d['As']]
alpha = list(d['alpha'])
while len(Bs[0]) < s_new:
    s = len(Bs[0])
    for j in range(L):
        cand = [y for y in range(NP) if y not in set(Bs[j].tolist())]
        y = rng.choice(cand)
        Bs[j] = np.append(Bs[j], y)
        As[j] = np.append(As[j], y)
    alpha = alpha + [s]
    rng.shuffle(alpha)
s = s_new
st = (M, Bs, As, alpha)
print('start bad', bad_pairs(build_adj(s, M, Bs, As, alpha)), flush=True)
best = anneal(s, iters, rng, T0=1.0, T1=0.05, state=st)
print(json.dumps({'s': s, 'seed': seed, 'bad': best[0]}), flush=True)
if best[0] == 0:
    with open(out, 'w') as f:
        json.dump({'s': s, 'bad': 0, 'M': [m.tolist() for m in best[1]], 'Bs': [b.tolist() for b in best[2]],
                   'As': [a.tolist() for a in best[3]], 'alpha': best[4]}, f)
