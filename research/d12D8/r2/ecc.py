import sys, collections
f = open(sys.argv[1]); nv = int(f.readline()); adj = [[] for _ in range(nv)]
for line in f:
    a, b = map(int, line.split()); adj[a].append(b); adj[b].append(a)
C, N1 = int(sys.argv[2]), int(sys.argv[3])
def bfs(s):
    d = [-1] * nv; d[s] = 0; dq = collections.deque([s])
    while dq:
        x = dq.popleft()
        for y in adj[x]:
            if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
    return d
def cls(v): return 'hub' if v >= C * N1 else 'copy'
for s in [0, 5, N1 // 2 + 3, C * N1, C * N1 + 7, C * N1 + 5 * (N1 // 2) + 2]:
    d = bfs(s); e = max(d); far = [v for v in range(nv) if d[v] == e]
    print(cls(s), s, 'ecc', e, 'far classes', collections.Counter(cls(v) for v in far))
