# count non-backtracking walks of length <= 9 from root 0 to each vertex, grouped by graph distance
from collections import defaultdict, deque
E = [tuple(map(int, l.split())) for l in open('base.txt').read().split('\n')[1:] if l.strip()]
N = 728
adj = [[] for _ in range(N)]
for u, v in E: adj[u].append(v); adj[v].append(u)
dist = [-1]*N; dist[0] = 0; q = deque([0])
while q:
    x = q.popleft()
    for y in adj[x]:
        if dist[y] < 0: dist[y] = dist[x]+1; q.append(y)
cnt = defaultdict(lambda: defaultdict(int))  # cnt[length][vertex]
# DFS over non-backtracking walks
def dfs(x, prev, L):
    cnt[L][x] += 1
    if L == 9: return
    for y in adj[x]:
        if y != prev: dfs(y, x, L+1)
dfs(0, -1, 0)
for L in range(0, 10):
    pass
# walks of length <= 8 (same side as root: even) and <= 9 (opposite side: odd) per distance class
tot = defaultdict(lambda: defaultdict(list))
for x in range(N):
    w = sum(cnt[L][x] for L in range(0, 10) if (L % 2) == (dist[x] % 2))
    tot[dist[x]]['walks_same_parity_le9'].append(w)
for d in sorted(tot):
    v = tot[d]['walks_same_parity_le9']
    print("dist", d, "vertices", len(v), "walks(parity-matched, <=9): min", min(v), "avg", round(sum(v)/len(v), 2), "max", max(v))
for d in (2, 4, 6):
    print("length-6 walks to dist-6 targets sample:", [cnt[6][x] for x in range(N) if dist[x] == 6][:10])
