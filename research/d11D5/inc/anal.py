"""Classify the structural failures of a DM base (plusopt format): for each failing (source, target, coset) print
the pure distance, pure walk counts of length 4/5, and whether any jumped walk exists.  usage: python3 anal.py in.txt"""
import sys, numpy as np
from collections import Counter
f = open(sys.argv[1]).read().split()
n, dg = int(f[0]), int(f[1]); V = 2 * n
ln = np.array(f[2:2 + n * dg], dtype=int).reshape(n, dg); sig = np.array(f[2 + n * dg:2 + n * dg + n], dtype=int)
B = np.zeros((V, V))
for l in range(n):
    for p in ln[l]: B[p, n + l] += 1; B[n + l, p] += 1
A = np.zeros((3 * V, 3 * V))   # state (v, c) -> index c*V + v
for c in range(3):
    A[c * V:(c + 1) * V, c * V:(c + 1) * V] = B
    for p in range(n):
        l = n + sig[p]
        A[c * V + p, ((c + 1) % 3) * V + l] = 1      # point -> line jump +1
        A[c * V + l, ((c - 1) % 3) * V + p] = 1      # line -> point jump -1
P = [np.eye(V)]; T = [np.hstack([np.eye(V), np.zeros((V, 2 * V))])]
for k in range(1, 6):
    P.append(P[-1] @ B); T.append(T[-1] @ A)
reach = sum(T[k] for k in range(6))
pure = sum(P[k] for k in range(6))
jumped0 = reach[:, :V] - pure
dist = np.full((V, V), 99)
for k in range(5, -1, -1): dist[P[k] > 0] = k
cnt = Counter(); ex = []
for s in range(V):
    for t in range(V):
        same = (s < n) == (t < n)
        ok0 = dist[s, t] <= (2 if same else 3) or jumped0[s, t] > 0.5 or (P[4][s, t] >= 2 if same else P[5][s, t] >= 2)
        for c, ok in ((0, ok0), (1, reach[s, V + t] > 0.5), (2, reach[s, 2 * V + t] > 0.5)):
            if not ok:
                key = (c, "PP" if s < n and t < n else "LL" if s >= n and t >= n else "PL", min(dist[s, t], 9), int(P[4][s, t] if same else P[5][s, t]))
                cnt[key] += 1
                if len(ex) < 4000: ex.append((s, t, key))
print("total", sum(cnt.values()))
for k, v in sorted(cnt.items(), key=lambda x: -x[1])[:30]: print(k, v)
for e in ex[:int(sys.argv[2]) if len(sys.argv) > 2 else 10]: print(e)
