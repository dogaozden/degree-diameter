import sys, random
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-65/c8')
from g2grp import *
from collections import deque
NV = P + L
adj = [[] for _ in range(NV)]
for k, l in enumerate(lines):
    for z in l:
        adj[z].append(P+k); adj[P+k].append(z)
def ball(s, r):
    d = {s: 0}; q = deque([s])
    while q:
        u = q.popleft()
        if d[u] == r: continue
        for w in adj[u]:
            if w not in d: d[w] = d[u]+1; q.append(w)
    return d
rng = random.Random(1)
best = 0
for trial in range(20):
    order = list(range(P)); rng.shuffle(order)
    cand = set(range(P)); chosen = []
    for x in order:
        if x not in cand: continue
        chosen.append(x)
        b = ball(x, 4)
        cand = {y for y in cand if y in b and y != x}
    best = max(best, len(chosen))
print("greedy max pairwise non-opposite point set (random orders), best:", best, flush=True)
