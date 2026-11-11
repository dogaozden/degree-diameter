import sys, collections
fn = sys.argv[1]; srcs = [int(x) for x in sys.argv[2:]]
f = open(fn); n = int(f.readline()); adj = [[] for _ in range(n)]
for l in f:
    u, v = map(int, l.split()); adj[u].append(v); adj[v].append(u)
H = 16896; n0 = 2 * H
def side(x):
    # BFS colouring from vertex 0
    pass
col = [-1] * n; col[0] = 0; q = [0]
for x in q:
    for y in adj[x]:
        if col[y] < 0: col[y] = 1 - col[x]; q.append(y)
for s in srcs:
    d = [-1] * n; d[s] = 0; q = [s]
    for x in q:
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; q.append(y)
    far = [x for x in range(n) if d[x] < 0 or d[x] > (4 if col[x] == col[s] else 5)]
    old = [x for x in far if x < n0]; new = [x for x in far if x >= n0]
    fib = collections.Counter((x // 256) for x in old)
    print(f"src {s} side {col[s]} deg {len(adj[s])}: far {len(far)} (old {len(old)}, new {len(new)}); old far by fibre (fibre id: count) {sorted(fib.items(), key=lambda t: -t[1])[:8]}; new far sample {new[:5]}")
