"""Conjugacy classes of cyclic subgroups of G (BFS under conjugation by two random elements of G that generate G)."""
import numpy as np, json, random
G = np.load('/home/user/degree-diameter/research/squads/gqd5-r3/c2/group.npy').astype(np.int32)
n = G.shape[1]; ident = np.arange(n, dtype=np.int32)
cyc = json.load(open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/cyclic_subgroups.json'))
def powers(g):
    pw = [ident]; cur = g
    while cur.tobytes() != ident.tobytes():
        pw.append(cur); cur = g[cur]
    return pw
def key(g): return frozenset(p.tobytes() for p in powers(g))
keys = {}
for i, c in enumerate(cyc):
    keys[key(G[c['gen']])] = i
def inv(s):
    r = np.empty_like(s); r[s] = np.arange(n, dtype=np.int32); return r
# choose generators of G
random.seed(1)
def gen_order(gs):
    seen = {ident.tobytes()}; fr = [ident]
    while fr:
        nf = []
        for x in fr:
            for s in gs:
                y = s[x]
                if y.tobytes() not in seen: seen.add(y.tobytes()); nf.append(y)
        fr = nf
    return len(seen)
while True:
    gs = [G[random.randrange(len(G))] for _ in range(2)]
    if gen_order(gs) == len(G): break
print('generators chosen', flush=True)
cls = [-1] * len(cyc); reps = []
for i in range(len(cyc)):
    if cls[i] >= 0: continue
    c = len(reps); reps.append(i); cls[i] = c; stack = [i]
    while stack:
        j = stack.pop()
        g = G[cyc[j]['gen']]
        for s in gs:
            h = s[g[inv(s)]]
            k = keys[key(h)]
            if cls[k] < 0: cls[k] = c; stack.append(k)
print('conjugacy classes of cyclic subgroups', len(reps), flush=True)
json.dump({'cls': cls, 'reps': reps}, open('/home/user/degree-diameter/research/squads/gqd5-r3/c2/cyclic_classes.json', 'w'))
from collections import Counter
print(sorted(Counter(cyc[r]['order'] for r in reps).items()))
