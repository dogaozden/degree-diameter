"""Theorem B (Theorem C before the 25 October revision) at a friendly transition for larger q (job thm-d7): two levels, level 0 of type H and level 1 of type D,
matching (p, 0) ~ (p, 1) for every point p not in F, F = all points of the Hermitian spread (q prime). Main graph, no hubs.
usage: python3 friendly_test.py HEXBIN OUT.edges   (hexagon from research/d10D7/hexgen2.c)"""
import sys
import numpy as np
raw = np.fromfile(sys.argv[1], dtype=np.uint8)
q, N, L = (int(x) for x in np.frombuffer(raw[:12].tobytes(), dtype=np.int32))
Q1 = q + 1
LP = np.frombuffer(raw[12:12 + 4 * L * Q1].tobytes(), dtype=np.int32).reshape(L, Q1)
co = raw[12 + 4 * L * Q1:].reshape(N, 7).astype(np.int64)
spread = None
for c in range(q):
    for e in range(q):
        inside = (co[:, 0] - c * co[:, 4] - e * co[:, 3]) % q == 0
        if inside.sum() == (q + 1) * (q ** 3 + 1):
            S = np.where(inside[LP].all(axis=1))[0]
            if len(S) == q ** 3 + 1: spread = (c, e, S); break
    if spread: break
c, e, S = spread
F = np.zeros(N, dtype=bool); F[LP[S].ravel()] = True
# segment property: no point of F has F-points on two lines; for a spread this means the lines are pairwise disjoint and
# no F-point is collinear with an F-point of another spread line. Check: every line not in S meets <= 1 point of F.
cnt = F[LP].sum(axis=1)
inS = np.zeros(N, dtype=bool); inS[S] = True
seg = bool((cnt[~inS] <= 1).all() and (cnt[inS] == Q1).all())
print(f'q={q} N={N}: spread in x0 = {c} x4 + {e} x3: {len(S)} lines; |F| = {F.sum()} = (q+1)(q^3+1) = {(q+1)*(q**3+1)}; '
      f'every line off the spread meets F at most once: {seg}')
V = 4 * N
with open(sys.argv[2], 'w') as f:
    f.write(f'{V}\n')
    for lev in range(2):
        b = lev * 2 * N
        for l in range(N):
            for p in LP[l]: f.write(f'{b + p} {b + N + l}\n')
    for p in np.where(~F)[0]: f.write(f'{p} {2 * N + p}\n')
print(f'two levels H -> D, identity on points minus F: n = {V}, wrote {sys.argv[2]}')
