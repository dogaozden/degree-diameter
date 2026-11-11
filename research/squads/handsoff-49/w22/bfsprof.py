import sys, collections
f = open(sys.argv[1]); n = int(f.readline())
adj = [[] for _ in range(n)]
for line in f:
    u, v = map(int, line.split()); adj[u].append(v); adj[v].append(u)
src = int(sys.argv[2]) if len(sys.argv) > 2 else 0
dist = [-1]*n; dist[src] = 0; q = collections.deque([src])
while q:
    u = q.popleft()
    for w in adj[u]:
        if dist[w] < 0: dist[w] = dist[u] + 1; q.append(w)
cnt = collections.Counter(dist)
print("layers", [cnt[i] for i in range(max(dist)+1)], "unreached", cnt[-1])
cross = sum(1 for u in range(n) for v in adj[u] if u//728 != v//728 and u < v)
print("cross edges", cross, "deg set", set(len(a) for a in adj))
