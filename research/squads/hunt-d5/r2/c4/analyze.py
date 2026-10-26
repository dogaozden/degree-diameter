import sys
from itertools import combinations
L = open(sys.argv[1]).read().split('\n'); n = int(L[0]); m = n // 2
nb = [set() for _ in range(n)]
for l in L[1:]:
    t = l.split()
    if len(t) >= 2:
        u, v = int(t[0]), int(t[1]); nb[u].add(v); nb[v].add(u)
def walk(s, k):
    cur = {s}
    for _ in range(k):
        cur = set().union(*[nb[x] for x in cur])
    return cur
far = []
for lo in (0, m):
    for s, t in combinations(range(lo, lo + m), 2):
        if t not in walk(s, 4): far.append((s, t))
no4 = [x for x in range(n) if not any(len(nb[a] & nb[b] - {x}) >= 1 for a, b in combinations(nb[x], 2))]
print("degrees", set(len(x) for x in nb), "far pairs", len(far), far[:10], "no4 vertices", no4)
