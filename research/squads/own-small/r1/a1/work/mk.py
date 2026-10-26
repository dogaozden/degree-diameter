import sys, numpy as np, itertools
G = "/home/user/degree-diameter/research/squads/own-small/seeds/groups/g220_2.txt"
tok = open(G).read().split()
N = int(tok[1]); assert tok[0] == "G" and int(tok[2]) == 2
M = np.array(list(map(int, tok[4:4 + N * N])), dtype=np.int64).reshape(N, N)
inv = [int(np.where(M[g] == 0)[0][0]) for g in range(N)]
np.array([N], dtype=np.int32).tofile("groups/g220_2.bin"); M.astype(np.uint16).tofile("groups/g220_2.bin", sep="") if False else None
with open("groups/g220_2.bin", "wb") as f:
    np.array([N], dtype=np.int32).tofile(f); M.astype(np.uint16).tofile(f)
# associativity spot check
rng = np.random.default_rng(1)
for _ in range(20000):
    a, b, c = rng.integers(0, N, 3)
    assert M[M[a, b], c] == M[a, M[b, c]]
# subgroups by <=2 generators
def closure(gens):
    H = {0}; frontier = [0]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = int(M[x, g])
                if y not in H: H.add(y); nf.append(y)
        frontier = nf
    return frozenset(H)
subs = set()
cyc = {}
for g in range(N):
    cyc.setdefault(closure([g]), g)
subs |= set(cyc)
cl = list(cyc)
for A in cl:
    for g in range(N):
        if g not in A:
            subs.add(closure(list(A)[:0] + [g] + [x for x in A if x != 0][:0]))
# full generation: iterate joining
changed = True
subs = set(subs)
while changed:
    changed = False
    cur = list(subs)
    for A in cur:
        for B in cur:
            if len(A) * len(B) < N * 2 and False: continue
            C = closure(list(A | B)[:0] + [x for x in B if True][:0] or [])  # placeholder
    break
from collections import Counter
print("cyclic subgroup orders:", sorted(Counter(len(H) for H in cl).items()))
gens_small = {}
for H in subs: pass
import pickle
pickle.dump(None, open("work/_", "wb"))
