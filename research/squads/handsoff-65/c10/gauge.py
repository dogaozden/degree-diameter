# gauge.py IN OUT M: abelian Z_M gauge normalisation: BFS tree from 0 (edge order), tree edges get voltage 0.
# lift (u,h)~(w,h+t) relabelled by h -> h+p(v): t' = t + p(w) - p(u); choose p along the tree.
import sys
from collections import deque
inf, outf, M = sys.argv[1], sys.argv[2], int(sys.argv[3])
L = open(inf).read().split('\n')
b, E = map(int, L[0].split()[:2])
side = L[1]
ed = []
for line in L[2:2 + E]:
    p = line.split(); ed.append([int(p[0]), int(p[1]), int(p[2]) if len(p) > 2 else 0])
adj = [[] for _ in range(b)]
for i, (u, w, t) in enumerate(ed):
    adj[u].append(i); adj[w].append(i)
pot = [None] * b; pot[0] = 0; q = deque([0]); tree = set()
while q:
    x = q.popleft()
    for i in adj[x]:
        u, w, t = ed[i]
        y = w if u == x else u
        if pot[y] is None:
            # for u->w with volt t: t' = t + p(w) - p(u) = 0 => p(w) = p(u) - t
            if x == u: pot[y] = (pot[x] - t) % M
            else: pot[y] = (pot[x] + t) % M
            tree.add(i); q.append(y)
assert all(p is not None for p in pot), "base not connected"
out = [f"{b} {E}", side]
for i, (u, w, t) in enumerate(ed):
    tt = (t + pot[w] - pot[u]) % M
    if i in tree: assert tt == 0
    out.append(f"{u} {w} {tt}")
open(outf, 'w').write('\n'.join(out) + '\n')
print("tree edges", len(tree), "ok")
