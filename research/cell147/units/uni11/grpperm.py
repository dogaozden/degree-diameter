# Orbits on E_q (prime q, data/E{q}.map) of a subgroup K of SL(2,q) acting on V4 = (x1,x2,x5,x6) ~ X = [[x1,x2],[-x6,x5]]
# (det form) by right (R) or left (L) multiplication, identity on A = (x0,x3). K is found by random 2-generation with
# |K| = ORDER. Output: a permutation whose cycles are the K-orbits (input for orbitclique_q).
# Usage: python3 grpperm.py q ORDER R|L SEED OUT
import sys, random
import numpy as np
q, order, side, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), sys.argv[5]
random.seed(seed)
def mul(a, b): return ((a[0]*b[0]+a[1]*b[2]) % q, (a[0]*b[1]+a[1]*b[3]) % q, (a[2]*b[0]+a[3]*b[2]) % q, (a[2]*b[1]+a[3]*b[3]) % q)
I = (1, 0, 0, 1)
def rand_sl2():
    while True:
        a = tuple(random.randrange(q) for _ in range(4))
        if (a[0]*a[3]-a[1]*a[2]) % q == 1: return a
def closure(gens, cap):
    S = {I}; frontier = [I]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in S:
                    S.add(y); nf.append(y)
                    if len(S) > cap: return None
        frontier = nf
    return S
K = None
for t in range(200000):
    g, h = rand_sl2(), rand_sl2()
    S = closure([g, h], order)
    if S is not None and len(S) == order: K = sorted(S); gens = [g, h]; break
if K is None: print("no subgroup found"); sys.exit(1)
tr2 = sum(1 for k in K if k != I and (k[0] + k[3]) % q == 2)
print(f"q={q} |K|={len(K)} gens={gens} nontrivial trace-2 elements: {tr2}")
rows = np.loadtxt(f'/home/user/degree-diameter/research/cell147/data/E{q}.map', dtype=np.int64)
X = rows[:, 2:9] % q; N = len(X)
INV = [0] + [pow(a, q - 2, q) for a in range(1, q)]
def norm(A):
    first = np.argmax(A != 0, axis=1); lead = A[np.arange(len(A)), first]
    return (A * np.array(INV)[lead][:, None]) % q
PW = q ** np.arange(7)
key = {int(v): i for i, v in enumerate(norm(X) @ PW)}
def act(k):
    k11, k12, k21, k22 = k
    Y = X.copy(); x1, x2, x5, x6 = X[:, 1], X[:, 2], X[:, 5], X[:, 6]
    if side == 'R':   # X k
        Y[:, 1] = x1 * k11 + x2 * k21; Y[:, 2] = x1 * k12 + x2 * k22
        Y[:, 6] = x6 * k11 - x5 * k21; Y[:, 5] = -x6 * k12 + x5 * k22
    else:             # k X: [[k11 x1 - k12 x6, k11 x2 + k12 x5], [k21 x1 - k22 x6, k21 x2 + k22 x5]]
        Y[:, 1] = k11 * x1 - k12 * x6; Y[:, 2] = k11 * x2 + k12 * x5
        Y[:, 6] = -(k21 * x1 - k22 * x6); Y[:, 5] = k21 * x2 + k22 * x5
    Y %= q
    return np.array([key[int(v)] for v in norm(Y) @ PW])
gp = [act(g) for g in gens]
# orbits by union-find over generator permutations
par = list(range(N))
def find(x):
    while par[x] != x: par[x] = par[par[x]]; x = par[x]
    return x
for p_ in gp:
    for i in range(N):
        a, b = find(i), find(int(p_[i]))
        if a != b: par[a] = b
orbs = {}
for i in range(N): orbs.setdefault(find(i), []).append(i)
perm = np.arange(N)
for o in orbs.values():
    for j in range(len(o)): perm[o[j]] = o[(j + 1) % len(o)]
np.savetxt(out, perm, fmt='%d')
from collections import Counter
print("orbit sizes:", sorted(Counter(len(o) for o in orbs.values()).items()))
