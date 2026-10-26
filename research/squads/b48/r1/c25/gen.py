# Generate base multigraphs for c25: biaffine plane (AG(2,4) minus one parallel class) and Levi graphs of
# cyclic (v_4) configurations {i, i+a, i+b, i+c} mod v. Reports girth, diameter, and writes base files.
import sys, itertools, collections, os
OUT = "/home/user/degree-diameter/research/squads/b48/r1/c25/bases"
os.makedirs(OUT, exist_ok=True)

def bfs(adj, s):
    d = {s: 0}; q = collections.deque([s])
    while q:
        u = q.popleft()
        for w in adj[u]:
            if w not in d:
                d[w] = d[u] + 1; q.append(w)
    return d

def stats(b, edges):
    adj = [[] for _ in range(b)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    diam = 0; girth = 10**9
    for s in range(b):
        d = bfs(adj, s)
        if len(d) < b:
            return None
        diam = max(diam, max(d.values()))
    # girth: min over edges (u,v) of shortest cycle through the edge, via BFS with edge removal
    for (u, v) in edges:
        adj[u].remove(v); adj[v].remove(u)
        d = bfs(adj, u)
        if v in d:
            girth = min(girth, d[v] + 1)
        adj[u].append(v); adj[v].append(u)
    return diam, girth

def write(name, b, edges):
    with open(os.path.join(OUT, name), "w") as f:
        f.write(f"{b} {len(edges)}\n")
        for u, v in edges:
            f.write(f"{u} {v}\n")

# biaffine plane: GF(4) = {0,1,2,3} with 2 = w, 3 = w+1, w^2 = w+1
def gmul(a, b):
    r = 0
    for i in range(2):
        if (b >> i) & 1: r ^= a << i
    if r & 4: r ^= 0b111  # reduce x^2 -> x+1
    return r
edges = []
for m in range(4):          # 4 non-vertical slopes (vertical class removed)
    for c in range(4):      # intercept
        line = 4 * m + c    # line index 0..15 (right side)
        for x in range(4):
            y = c ^ gmul(m, x)
            pt = 4 * x + y  # point index 0..15 (left side)
            edges.append((pt, 16 + line))
s = stats(32, edges)
print("biaffine", s)
write("biaffine32.txt", 32, edges)
res = {"biaffine32.txt": (32, s)}

# Levi graphs of cyclic configurations
cands = {}
for v in range(15, 41):
    best = None
    for a, b_, c in itertools.combinations(range(1, v), 3):
        S = (0, a, b_, c)
        # need 12 differences distinct and nonzero mod v (girth >= 6)
        diffs = [(x - y) % v for x in S for y in S if x != y]
        if len(set(diffs)) != 12:
            continue
        edges = []
        for i in range(v):
            for s_ in S:
                edges.append(((i + s_) % v, v + i))
        st = stats(2 * v, edges)
        if st is None:
            continue
        diam, girth = st
        key = (diam, -girth)
        if best is None or key < best[0]:
            best = (key, S, edges, st)
    if best:
        _, S, edges, st = best
        name = f"levi_v{v}_S{'_'.join(map(str,S))}.txt"
        write(name, 2 * v, edges)
        res[name] = (2 * v, st)
        print(name, 2 * v, st, flush=True)
