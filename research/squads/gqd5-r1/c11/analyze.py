"""Diagnose the bad pairs (distance > 5) of an allH edge file for q=4, r=1 or 2.
usage: python3 analyze.py EDGEFILE q r"""
import sys, collections
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib
from duality import duality

path, q, r = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
G, phi_pt, phi_line = duality(q)
per = G.np + G.nl
n_lev = 2 * r + 1
nv = n_lev * per
with open(path) as f:
    n = int(f.readline())
    E = [tuple(map(int, l.split())) for l in f if l.strip()]
adj = [[] for _ in range(n)]
for a, b in E:
    adj[a].append(b); adj[b].append(a)

def name(v):
    if v < nv:
        j, w = divmod(v, per)
        return ('L%d' % j) + ('pt%d' % w if w < G.np else 'ln%d' % (w - G.np))
    if v < nv + r * (q * q + 1):
        return 'Bhub%d' % (v - nv)
    return 'Ahub%d' % (v - nv - r * (q * q + 1))

def bfs(s):
    dist = [-1] * n; dist[s] = 0; dq = collections.deque([s])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if dist[w] < 0:
                dist[w] = dist[u] + 1; dq.append(w)
    return dist

cnt = collections.Counter()
examples = {}
for s in range(n):
    d = bfs(s)
    for t in range(s + 1, n):
        if d[t] > 5:
            key = (name(s).split('pt')[0].split('ln')[0][:6] if False else '', d[t])
            ks = (name(s)[:2] if name(s)[0] == 'L' else name(s)[:4], name(t)[:2] if name(t)[0] == 'L' else name(t)[:4], d[t])
            cnt[ks] += 1
            examples.setdefault(ks, (name(s), name(t)))
print('bad pairs by type (src,dst,dist): count, example')
for k, v in sorted(cnt.items()):
    print(k, v, examples[k])
print('total bad unordered pairs', sum(cnt.values()))
