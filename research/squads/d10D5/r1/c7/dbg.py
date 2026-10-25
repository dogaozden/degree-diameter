import random, collections, sys
sys.argv=['x','1','/dev/null']
exec(open('gq79_lift.py').read().split("seed = int")[0])   # reuse GQ construction (points, lines, point_lines)
rng = random.Random(1)
base = []
for p in range(512):
    for j in point_lines[p]:
        base.append((p, 512 + j, rng.choice([0, 2, 4])))
order = list(range(640)); rng.shuffle(order)
for i in range(640):
    a, b = order[i], order[(i + 1) % 640]
    base.append((512 + a, 512 + b, rng.choice([1, 3, 5])))
# base adjacency with voltages (oriented edge u->v carries g, v->u carries -g)
adj = collections.defaultdict(list)
for (u, v, g) in base:
    adj[u].append((v, g % 6)); adj[v].append((u, (-g) % 6))
# walks of length exactly 4 from point 0 to far points, with voltage sums (non-backtracking in base)
v0 = 0
walks = collections.defaultdict(list)   # target -> list of (length, voltage)
def dfs(x, prev, L, volt, path):
    if L > 0 and x < 512 and L % 2 == 0:
        walks[x].append((L, volt))
    if L == 4:
        return
    for (y, g) in adj[x]:
        if y == prev and L>0:  # forbid immediate backtrack along same base edge (approx.)
            continue
        dfs(y, x, L + 1, (volt + g) % 6, path + [y])
dfs(v0, None, 0, 0, [v0])
# far points: those with no walk of length 2 (collinear points have length-2 walks)
far = [u for u in range(512) if u != v0 and not any(L == 2 for (L, _) in walks[u])]
print("far points", len(far))
cnt = collections.Counter()
for u in far[:50]:
    ws = [w for w in walks[u] if w[0] == 4]
    vals = collections.Counter(v for (_, v) in ws)
    cnt[len(ws)] += 1
print("walks of length 4 to far points (count distribution, first 50):", sorted(cnt.items()))
u = far[0]
print("example far point", u, "length-4 walk voltages:", sorted(v for (L, v) in walks[u] if L == 4))
miss = 0; missing_hist = collections.Counter()
for u in far:
    vals = set(v for (L, v) in walks[u] if L == 4)
    m = [h for h in (0, 2, 4) if h not in vals]
    miss += len(m); missing_hist[len(m)] += 1
print("total missed phi=0 values over far points (length-4 walks only):", miss, dict(missing_hist))
# same for the other parity class using length-5 walks is not computed here; check point->point via BFS up to 5 in base
