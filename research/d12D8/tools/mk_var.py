"""Variants of hexagon + 2 hops at Z_5 levels (+1,+2), optional Z_m second factor (random), output liftcheck base.
Mvariant: 'rand' (two random bijections), 'same' (M2 = M1 random), 'inc' (two random perfect matchings of the
incidence graph, i.e. hop to a line through the point), 'inc1' (M1 incidence matching, M2 random), 'incsame' (M2=M1 incidence).
usage: mk_var.py q Mvariant m2 seed out  (group Z_(5*m2) via CRT, m2 coprime to 5; m2=1 gives pure Delorme X_2)"""
import sys, random
import numpy as np
from hexlib import load_hex, write_base
q, var, m2, seed, out = int(sys.argv[1]), sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
random.seed(seed)
n, lines = load_hex(q)
N = 5 * m2
def crt(a, b):
    for x in range(N):
        if x % 5 == a % 5 and x % m2 == b % m2: return x
pl = [[] for _ in range(n)]
for l in range(n):
    for p in lines[l]: pl[p].append(l)
def rand_bij():
    perm = list(range(n)); random.shuffle(perm); return perm
def inc_matching():
    # random perfect matching of the (q+1)-regular bipartite incidence graph: greedy + augmenting (Hopcroft-Karp light)
    order = list(range(n)); random.shuffle(order)
    matchL = [-1] * n; matchP = [-1] * n
    adj = [random.sample(pl[p], len(pl[p])) for p in range(n)]
    for p in order:
        for l in adj[p]:
            if matchL[l] < 0: matchL[l] = p; matchP[p] = l; break
    # augment
    import collections
    free = [p for p in range(n) if matchP[p] < 0]
    for p0 in free:
        # BFS for augmenting path
        prev = {}; dq = collections.deque([p0]); seen_l = set(); found = None
        while dq and found is None:
            p = dq.popleft()
            for l in adj[p]:
                if l in seen_l: continue
                seen_l.add(l); prev[l] = p
                if matchL[l] < 0: found = l; break
                dq.append(matchL[l])
        l = found
        while l is not None:
            p = prev[l]; nl = matchP[p]; matchP[p] = l; matchL[l] = p; l = nl if nl != -1 else None
    assert all(x >= 0 for x in matchP)
    return matchP
if var == 'rand': M1, M2 = rand_bij(), rand_bij()
elif var == 'same': M1 = rand_bij(); M2 = M1
elif var == 'inc': M1, M2 = inc_matching(), inc_matching()
elif var == 'inc1': M1, M2 = inc_matching(), rand_bij()
elif var == 'incsame': M1 = inc_matching(); M2 = M1
E = []
for l in range(n):
    for p in lines[l]: E.append((int(p), l, crt(0, random.randrange(m2))))
for p in range(n):
    E.append((p, M1[p], crt(1, random.randrange(m2))))
    E.append((p, M2[p], crt(2, random.randrange(m2))))
write_base(out, n, E, N)
