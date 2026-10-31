# closed and total non-backtracking walk counts (length <= 9) from a root in pg23.txt
from collections import defaultdict
E = [tuple(map(int, l.split())) for l in open('pg23.txt').read().split('\n')[1:] if l.strip()]
N = 26
adj = [[] for _ in range(N)]
for u, v in E: adj[u].append(v); adj[v].append(u)
cnt = defaultdict(lambda: defaultdict(int))
def dfs(x, prev, L, root):
    cnt[L][x] += 1
    if L == 9: return
    for y in adj[x]:
        if y != prev: dfs(y, x, L+1, root)
dfs(0, -1, 0, 0)
for L in range(0, 10):
    print("length", L, "NB walks from root", sum(cnt[L].values()), "closed at root", cnt[L][0], "to same side (points)", sum(cnt[L][x] for x in range(13)), "to lines", sum(cnt[L][x] for x in range(13,26)))
