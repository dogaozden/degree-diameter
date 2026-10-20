"""Structure of the exact whisker sets found by hex_small.py (whiskers_q{q}.json)."""
import json
import sys
from collections import Counter, deque

from lift import ROOT
sys.path.insert(0, str(ROOT / 'research' / 'gh6'))
import gh_build  # noqa: E402

q = int(sys.argv[1])
d = json.load(open(ROOT / 'research' / 'p4' / 'hats' / f'whiskers_q{q}.json'))
S, v, W, E = d['S'], d['v'], set(d['whiskers']), set(d['empty'])
N, lines = gh_build.hexagon(q)
through = [[] for _ in range(N)]
for k, L in enumerate(lines):
    for p in L:
        through[p].append(k)
V = 2 * N
adj = [[] for _ in range(V)]
for k, L in enumerate(lines):
    for p in L:
        adj[p].append(N + k)
        adj[N + k].append(p)
dist = [-1] * V
dist[N + v] = 0
dq = deque([N + v])
while dq:
    x = dq.popleft()
    for y in adj[x]:
        if dist[y] < 0:
            dist[y] = dist[x] + 1
            dq.append(y)
Sset = set(S)
Sline_of = {p: s for s in S for p in lines[s]}
onS = set(Sline_of)
free = [p for p in range(N) if p not in onS and dist[p] == 5]
stats = Counter()
for p in free:
    B = {}
    for k in through[p]:
        x = [y for y in lines[k] if y in onS][0]
        B[k] = Sline_of[x]
    toward = [k for k in through[p] if dist[N + k] == 4][0]
    wk = [k for k in through[p] if k in W]
    assert len(wk) == 1
    stats[(sum(1 for s in B.values() if s in E), B[toward] in E, B[wk[0]] in E)] += 1
print('free points', len(free), ' (|B(p) & E|, toward-line target empty?, whisker target empty?):')
for k, c in sorted(stats.items()):
    print('  ', k, c)
