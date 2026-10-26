# Independent check of the README rules (not po7): bitset walk DP over (vertex, coset, jumped) states.
import sys
import numpy as np
fn = sys.argv[1]
t = open(fn).read().split()
n, dg = int(t[0]), int(t[1])
L = [[int(t[2 + l * dg + k]) for k in range(dg)] for l in range(n)]
sig = [int(x) for x in t[2 + n * dg: 2 + n * dg + n]]
assert sorted(sig) == list(range(n)), "sigma not a bijection"
V = 2 * n
sinv = [0] * n
for p, l in enumerate(sig): sinv[l] = p
pure = [[] for _ in range(V)]
for l in range(n):
    for p in L[l]:
        pure[p].append(n + l); pure[n + l].append(p)
# degree check
deg = [0] * n
for l in range(n):
    assert len(set(L[l])) == dg
    for p in L[l]: deg[p] += 1
assert all(d == dg for d in deg), "point degree"
jump = [None] * V          # (target, shift)
for p in range(n): jump[p] = (n + sig[p], 1)
for l in range(n): jump[n + l] = (sinv[l], 2)     # -1 mod 3
# walk DP: R[v][c][j] = bitset of sources s with a walk s->v of current length, coset c, j = jumped flag
def step(R):
    N = [[[0, 0] for _ in range(3)] for _ in range(V)]
    for v in range(V):
        for c in range(3):
            for j in range(2):
                x = R[v][c][j]
                if not x: continue
                for w in pure[v]: N[w][c][j] |= x
                w, d = jump[v]; N[w][(c + d) % 3][1] |= x
    return N
R = [[[0, 0] for _ in range(3)] for _ in range(V)]
for s in range(V): R[s][0][0] |= 1 << s
U = [[[0, 0] for _ in range(3)] for _ in range(V)]
for v in range(V):
    U[v][0][0] |= R[v][0][0]
# pure-only exact-length reach P[k][v] (bitset of sources)
P = [[0] * V for _ in range(6)]
for s in range(V): P[0][s] |= 1 << s
for k in range(1, 6):
    for v in range(V):
        x = P[k - 1][v]
        if x:
            for w in pure[v]: P[k][w] |= x
for k in range(1, 6):
    R = step(R)
    for v in range(V):
        for c in range(3):
            for j in range(2): U[v][c][j] |= R[v][c][j]
# walk counts for the >=2 pure-walk clause
A = np.zeros((V, V), dtype=np.int64)
for v in range(V):
    for w in pure[v]: A[v, w] = 1
A4 = np.linalg.matrix_power(A, 4); A5 = np.linalg.matrix_power(A, 5)
fail = {1: 0, 2: 0, 0: 0}
for tv in range(V):
    for s in range(V):
        bit = 1 << s
        same = (s < n) == (tv < n)
        if s == tv: continue
        for c in (1, 2):
            if not ((U[tv][c][0] | U[tv][c][1]) & bit): fail[c] += 1
        ok = bool(U[tv][0][1] & bit)
        if not ok:
            if same:
                ok = bool(P[0][tv] & bit) or bool(P[2][tv] & bit) or A4[s, tv] >= 2
            else:
                ok = bool(P[1][tv] & bit) or bool(P[3][tv] & bit) or A5[s, tv] >= 2
        if not ok: fail[0] += 1
print(f"n={n} dg={dg} V={V} independent check: coset1 fails={fail[1]} coset2 fails={fail[2]} coset0 fails={fail[0]} total={sum(fail.values())}")
