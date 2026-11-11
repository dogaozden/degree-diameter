import sys
from collections import defaultdict
def run(fn):
    L0 = open(fn).read().split('\n')
    b, m = map(int, L0[0].split()[:2])
    E = [tuple(map(int, l.split()[:2])) for l in L0[1:1+m]]
    adj = [[] for _ in range(b)]
    for u, v in E: adj[u].append(v); adj[v].append(u)
    cnt = defaultdict(int)
    def dfs(x, prev, L):
        if L > 0 and x == 0: cnt[L] += 1
        if L == 9: return
        for y in adj[x]:
            if y != prev: dfs(y, x, L+1)
    dfs(0, -1, 0)
    print(fn, "b", b, "closed NB walks at root by length:", dict(cnt), "total<=9:", sum(cnt.values()))
for fn in sys.argv[1:]:
    run(fn)
