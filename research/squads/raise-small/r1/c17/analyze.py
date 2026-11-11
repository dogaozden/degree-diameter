import sys
from collections import deque, Counter
tab, base, best, D = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
toks = open(tab).read().split(); N = int(toks[1]); M = list(map(int, toks[4:4 + N * N]))
inv = [next(h for h in range(N) if M[g * N + h] == 0) for g in range(N)]
bt = open(base).read().split(); NB, NE = int(bt[0]), int(bt[1])
E = [(int(bt[2 + 2 * i]), int(bt[3 + 2 * i])) for i in range(NE)]
bl = open(best).read().split(); vol = list(map(int, bl[2:2 + NE]))
print("volts nonzero", sum(1 for x in vol if x), "distinct", len(set(vol)))
nbr = [[] for _ in range(NB)]
for (p, l), x in zip(E, vol):
    nbr[p].append((l, x)); nbr[l].append((p, inv[x]))
n = NB * N
for u in [0, 1, 40, 41]:
    dist = [-1] * n; s = u * N; dist[s] = 0; dq = deque([s])
    while dq:
        y = dq.popleft(); d = dist[y]
        b, g = divmod(y, N)
        for (v, x) in nbr[b]:
            z = v * N + M[g * N + x]
            if dist[z] < 0: dist[z] = d + 1; dq.append(z)
    hist = Counter(dist)
    unr = [z for z in range(n) if dist[z] < 0 or dist[z] > D]
    bases = Counter(z // N for z in unr)
    print("root", u, "ecc", max(dist), "dist hist", sorted(hist.items()), "beyond D", len(unr), "by base vertex", sorted(bases.items())[:12])
