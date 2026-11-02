# Tutte 8-cage = incidence graph of GQ(2,2): points = 15 pairs of {0..5}, lines = 15 synthemes (3 disjoint pairs).
# Output base8.txt: first line "n m", then "u v tree" lines (tree=1 for BFS spanning tree edges).
import itertools, collections, sys
pairs = [frozenset(p) for p in itertools.combinations(range(6), 2)]
def perfect_matchings(s):
    s = sorted(s)
    if not s: yield []; return
    a = s[0]
    for b in s[1:]:
        rest = [x for x in s if x not in (a, b)]
        for m in perfect_matchings(rest):
            yield [frozenset((a, b))] + m
synth = [frozenset(m) for m in perfect_matchings(range(6))]
assert len(synth) == 15
edges = []
for i, p in enumerate(pairs):
    for j, L in enumerate(synth):
        if p in L:
            edges.append((i, 15 + j))
n = 30
adj = collections.defaultdict(list)
for u, v in edges: adj[u].append(v); adj[v].append(u)
assert all(len(adj[u]) == 3 for u in range(n)) and len(edges) == 45
# BFS tree from 0
tree = set(); seen = {0}; q = collections.deque([0])
while q:
    u = q.popleft()
    for v in adj[u]:
        if v not in seen:
            seen.add(v); tree.add(frozenset((u, v))); q.append(v)
# girth and diameter
def bfs(s):
    d = {s: 0}; q = collections.deque([s])
    while q:
        u = q.popleft()
        for v in adj[u]:
            if v not in d: d[v] = d[u] + 1; q.append(v)
    return d
diam = max(max(bfs(s).values()) for s in range(n))
girth = min(min(bfs(s)[u] for u in []) if False else 99 for s in range(1)) # placeholder
g = 99
for (u, v) in edges:
    # shortest cycle through edge u-v: dist from u to v avoiding edge
    adj[u].remove(v); adj[v].remove(u)
    d = bfs2 = None
    dd = {u: 0}; q = collections.deque([u])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if y not in dd: dd[y] = dd[x] + 1; q.append(y)
    if v in dd: g = min(g, dd[v] + 1)
    adj[u].append(v); adj[v].append(u)
print("diameter", diam, "girth", g, "cotree", len(edges) - len(tree), file=sys.stderr)
with open("base8.txt", "w") as f:
    f.write(f"{n} {len(edges)}\n")
    for u, v in edges:
        f.write(f"{u} {v} {1 if frozenset((u, v)) in tree else 0}\n")
