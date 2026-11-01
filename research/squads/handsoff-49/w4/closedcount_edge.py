# closed walks at root 0 without immediately reusing the same edge (edge-level non-backtracking), length <= 9
import sys
from collections import defaultdict
def run(fn):
    L0 = open(fn).read().split('\n')
    b, m = map(int, L0[0].split()[:2])
    E = [tuple(map(int, l.split()[:2])) for l in L0[1:1+m]]
    inc = [[] for _ in range(b)]
    for j, (u, v) in enumerate(E):
        inc[u].append((v, j)); inc[v].append((u, j))
    cnt = defaultdict(int)
    def dfs(x, pe, L):
        if L > 0 and x == 0: cnt[L] += 1
        if L == 9: return
        for y, j in inc[x]:
            if j != pe: dfs(y, j, L+1)
    dfs(0, -1, 0)
    print(fn, "b", b, "m", m, "closed edge-NB walks by length:", dict(cnt), "total<=9:", sum(cnt.values()))
for fn in sys.argv[1:]:
    run(fn)
