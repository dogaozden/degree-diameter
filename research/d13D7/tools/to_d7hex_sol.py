#!/usr/bin/env python3
"""Translate an edge list written by build_d13D7.py into a d7hex solution file (research/squads/exp2/hexd7/d7hex.c
format: "d7hex q N K NV", "freed p1..pK", "hubedges m j k ...", then the matching M[0..N-1]) in hexgen.c indexing,
so that `d7hex edges hex_q11.bin SOL out` rebuilds the same graph.  Points: both programs order points by the code
sum x_i 11^i (checked through the coordinates); lines are matched through their point sets.
usage: to_d7hex_sol.py HEXBIN EDGES OUT.sol"""
import sys, numpy as np
sys.path.insert(0, __import__('os').path.dirname(__file__))
import hexlib

hexbin, edges, out = sys.argv[1:4]
q, lines, coord = hexlib.load(hexbin)
N = len(coord)
code = coord @ (q ** np.arange(7))
assert (np.diff(code) > 0).all(), 'hexgen points not sorted by code'
key = {tuple(sorted(int(x) for x in l)): i for i, l in enumerate(lines)}
with open(edges) as f:
    n = int(f.readline())
    E = np.loadtxt(f, dtype=np.int64)
K = (n - 6 * N) // 2
assert n == 6 * N + 2 * K
# builder lines: rebuild their point sets from the level-0 hexagon edges (point id < N, line id N..2N-1)
lvl0 = E[(E[:, 0] < N) & (E[:, 1] >= N) & (E[:, 1] < 2 * N)]
pts_of = {}
for p, l in lvl0:
    pts_of.setdefault(int(l) - N, []).append(int(p))
assert len(pts_of) == N
bl2h = np.empty(N, dtype=np.int64)
for lb, pts in pts_of.items():
    bl2h[lb] = key[tuple(sorted(pts))]
# matching: level-0 point p -> level-1 line
mt = E[(E[:, 0] < N) & (E[:, 1] >= 3 * N) & (E[:, 1] < 4 * N)]
M = -np.ones(N, dtype=np.int64)
M[mt[:, 0]] = bl2h[mt[:, 1] - 3 * N]
# hubs: v_j = 6N + j ~ (R_j, i); u_j = 6N + K + j ~ (S_j, i)
hubv = E[(E[:, 0] >= 6 * N) & (E[:, 0] < 6 * N + K) & (E[:, 1] < N)]
R = np.empty(K, dtype=np.int64); R[hubv[:, 0] - 6 * N] = hubv[:, 1]
hubu = E[(E[:, 0] >= 6 * N + K) & (E[:, 1] >= N) & (E[:, 1] < 2 * N)]
S = np.empty(K, dtype=np.int64); S[hubu[:, 0] - 6 * N - K] = bl2h[hubu[:, 1] - N]
assert (M[R] == -1).all()
M[R] = S
assert sorted(M.tolist()) == list(range(N)), 'M is not a bijection'
hg = E[(E[:, 0] >= 6 * N) & (E[:, 0] < 6 * N + K) & (E[:, 1] >= 6 * N + K)]
with open(out, 'w') as f:
    f.write(f'd7hex {q} {N} {K} {n}\nfreed ' + ' '.join(map(str, R.tolist())) + '\n')
    f.write(f'hubedges {len(hg)} ' + ' '.join(f'{a - 6 * N} {b - 6 * N - K}' for a, b in hg) + '\n')
    for i in range(0, N, 20):
        f.write(' '.join(map(str, M[i:i + 20].tolist())) + '\n')
print(f'wrote {out}: q={q} N={N} K={K} n={n} hubedges={len(hg)}')
