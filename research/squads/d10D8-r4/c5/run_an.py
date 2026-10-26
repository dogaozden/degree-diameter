import sys, random, collections
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
from analyze import residual
q = 3; H = load_hex(q); N = H["N"]; Q1 = H["Q1"]; pl = H["pl"]
sig1 = list(range(N)); sig2 = [(p + N // 3) % N for p in range(N)]
m = 20
hv = [(6 * pl[l * Q1 + k] * l) % m for l in range(N) for k in range(Q1)]
mv1 = [1] * N; mv2 = [6] * N
print("lift3 fullcost", evaluate(q, m, [sig1, sig2], [mv1, mv2], hv, tag="chk_idx"))
tot, unc, H = residual(q, m, [sig1, sig2], [mv1, mv2], hv)
print("python residual total", tot, "pairs", len(unc))
# classify pairs by type (point/line) and by H-distance (incidence graph BFS on base graph B)
V = 2 * N
from collections import deque
pos = {}
adjB = [[] for _ in range(V)]
for l in range(N):
    for k in range(Q1):
        p = pl[l * Q1 + k]; adjB[p].append(N + l); adjB[N + l].append(p)
for t, s in enumerate([sig1, sig2]):
    for p in range(N):
        adjB[p].append(N + s[p]); adjB[N + s[p]].append(p)
def bfs(x):
    d = [-1] * V; d[x] = 0; dq = deque([x])
    while dq:
        u = dq.popleft()
        for w in adjB[u]:
            if d[w] < 0: d[w] = d[u] + 1; dq.append(w)
    return d
cnt = collections.Counter(); byd = collections.Counter()
for x in range(0, V, 1):
    if x >= N: break   # sources: points only (lift is regular, lines symmetric enough for this count)
    d = bfs(x)
    for (xx, y), miss in unc.items():
        if xx != x: continue
        typ = "pt-pt" if y < N else "pt-ln"
        cnt[(typ, d[y])] += bin(miss).count("1")
print("uncovered triples by (type, base distance), points as sources:", sorted(cnt.items()))
ex = [(k, v) for k, v in unc.items()][:10]
print("examples", [(x, y, bin(v).count("1")) for (x, y), v in ex])
