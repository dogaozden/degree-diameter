# girth_h3.py : girth and diameter of the incidence graph of the seed hexagon H(3) (points vs lines), independent BFS.
import json
from collections import deque
d = json.load(open('/home/user/degree-diameter/research/squads/handsoff-49/seeds/hexagon_q3.json'))
P = d['points'] if isinstance(d['points'], int) else len(d['points']); L = d['lines'] if isinstance(d['lines'], int) else len(d['lines'])
adj = [[] for _ in range(P + L)]
LINES = d['lines'] if not isinstance(d['lines'], int) else []
for li, line in enumerate(LINES):
    for p in line:
        adj[p].append(P + li); adj[P + li].append(p)
degs = sorted(set(len(a) for a in adj))
girth = 10**9; diam = 0
for s in range(P + L):
    dist = [-1] * (P + L); par = [-1] * (P + L); dist[s] = 0; q = deque([s])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1; par[y] = x; q.append(y)
            elif par[x] != y:
                girth = min(girth, dist[x] + dist[y] + 1)
    diam = max(diam, max(dist))
print(f"q={d['q']} points={P} lines={L} vertex_degrees={degs} girth={girth} diameter={diam}")
