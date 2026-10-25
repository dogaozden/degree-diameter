import sys, collections
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d10D8-r4/c5")
from rule import *
from geo import *
from analyze import residual
from collections import deque
q = 3; G = geometry(q); N = G["N"]; Q1 = G["Q1"]; pl = G["pl"]
m = 20
rp, lr = G["rank_p"], G["line_of_rank"]
sh, iota, ma, mb = 28, [0, 16, 5, 9], 1, 14
s1 = [lr[rp[p]] for p in range(N)]
s2 = [lr[(rp[p] + sh) % N] for p in range(N)]
hv = [iota[G["tlab"][(l, k)]] for l in range(N) for k in range(Q1)]
mv1, mv2 = [ma] * N, [mb] * N
print("lift3", evaluate(q, m, [s1, s2], [mv1, mv2], hv, tag="rb"))
tot, unc, H = residual(q, m, [s1, s2], [mv1, mv2], hv)
print("residual total", tot, "pairs", len(unc))
V = 2 * N
adjB = [[] for _ in range(V)]
for l in range(N):
    for k in range(Q1):
        p = pl[l * Q1 + k]; adjB[p].append(N + l); adjB[N + l].append(p)
for s in (s1, s2):
    for p in range(N):
        adjB[p].append(N + s[p]); adjB[N + s[p]].append(p)
def bfs(x):
    d = [-1] * V; d[x] = 0; dq = deque([x])
    while dq:
        u = dq.popleft()
        for w in adjB[u]:
            if d[w] < 0: d[w] = d[u] + 1; dq.append(w)
    return d
for (x, y), miss in list(unc.items())[:12]:
    d = bfs(x)[y]
    levels = [h for h in range(m) if miss >> h & 1]
    print("x", x, "(pt)" if x < N else "(ln)", "y", y, "(pt)" if y < N else "(ln)", "dist", d, "missing levels", levels)
# how many pairs per (type,dist)
cnt = collections.Counter()
for (x, y), miss in unc.items():
    if x >= N: continue
    d = bfs(x)[y]
    cnt[("pt-pt" if y < N else "pt-ln", d)] += bin(miss).count("1")
print("by type/dist (points as source):", sorted(cnt.items()))
