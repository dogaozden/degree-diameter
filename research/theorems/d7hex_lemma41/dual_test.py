"""Corollary 8.2 / Theorem C test with a duality (job thm-d7): all levels of type H, every transition (j, j+k) matched by
a duality phi (p, j) ~ (phi(p), j+k), and F = all points of the Hermitian spread freed on every transition.
Hexagon: research/d10D7/hexgen2.c output; duality: research/d10D7/dual/dualfind.c output (.phi: 2N ints, phi(p) at p).
usage: python3 dual_test.py HEXBIN PHIFILE r OUT.edges [extra_point]
Prints |F|, the checks of the hypotheses, and writes the main graph (no hubs) as an apsp edge list. With extra_point,
that point is also freed (negative control: it breaks the segment property)."""
import sys
import numpy as np

hexbin, phifile, r, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
extra = int(sys.argv[5]) if len(sys.argv) > 5 else None
raw = np.fromfile(hexbin, dtype=np.uint8)
q, N, L = np.frombuffer(raw[:12].tobytes(), dtype=np.int32)
Q1 = q + 1
LP = np.frombuffer(raw[12:12 + 4 * L * Q1].tobytes(), dtype=np.int32).reshape(L, Q1)
coord = raw[12 + 4 * L * Q1:].reshape(N, 7).astype(np.int64)
assert q == 3, 'prime field arithmetic below assumes q prime'
phi = np.fromfile(phifile, dtype=np.int32)
assert len(phi) == 2 * N
# incidence graph, vertices: points 0..N-1, lines N..2N-1
nbr = [[] for _ in range(2 * N)]
for l in range(N):
    for p in LP[l]:
        nbr[p].append(N + l); nbr[N + l].append(int(p))
# phi is a duality: maps points to lines, lines to points, and preserves incidence
assert all(phi[p] >= N for p in range(N)) and all(phi[N + l] < N for l in range(N))
assert all(sorted(phi[y] for y in nbr[x]) == sorted(nbr[phi[x]]) for x in range(2 * N)), 'phi does not preserve incidence'
print(f'q={q} N={N}: phi is a duality (checked on all {N * Q1} incidences)')
# Hermitian spread: H(q)-lines inside a hyperplane x0 = c x4 + e x3 with elliptic section ((q+1)(q^3+1) points)
spread = None
for c in range(q):
    for e in range(q):
        inside = (coord[:, 0] - c * coord[:, 4] - e * coord[:, 3]) % q == 0
        if inside.sum() != (q + 1) * (q ** 3 + 1):
            continue
        S = [l for l in range(N) if inside[LP[l]].all()]
        if len(S) == q ** 3 + 1:
            spread = (c, e, S); break
    if spread: break
c, e, S = spread
# pairwise opposite: BFS distances from each spread line
def bfs(s):
    d = np.full(2 * N, -1); d[s] = 0; fr = [s]
    while fr:
        nx = []
        for x in fr:
            for y in nbr[x]:
                if d[y] < 0: d[y] = d[x] + 1; nx.append(y)
        fr = nx
    return d
opp = all(bfs(N + a)[N + b] == 6 for a in S for b in S if a != b)
F = sorted(set(int(p) for l in S for p in LP[l]))
print(f'Hermitian spread in x0 = {c} x4 + {e} x3: {len(S)} lines, pairwise opposite: {opp}; |F| = {len(F)} = (q+1)(q^3+1)')
if extra is not None:
    assert extra not in F
    F.append(extra)
Fs = set(F)
# segment property (Definition 1.3)
def seg_ok():
    for p in Fs:
        lines_with = [l for l in nbr[p] if any(y != p and y in Fs for y in nbr[l])]
        if len(lines_with) > 1: return False
    return True
print('segment set:', seg_ok())
Lv = 2 * r + 1
V = Lv * 2 * N
E = []
for j in range(Lv):
    for l in range(N):
        for p in LP[l]:
            E.append((j * 2 * N + int(p), j * 2 * N + N + l))
    for k in range(1, r + 1):
        j2 = (j + k) % Lv
        for p in range(N):
            if p not in Fs:
                E.append((j * 2 * N + p, j2 * 2 * N + int(phi[p])))
with open(out, 'w') as f:
    f.write(f'{V}\n')
    for a, b in E: f.write(f'{a} {b}\n')
print(f'levels {Lv} (all H), r = {r}, every transition matched by phi, |F| = {len(F)} freed on every transition: '
      f'n = {V}, edges = {len(E)}, wrote {out}')
