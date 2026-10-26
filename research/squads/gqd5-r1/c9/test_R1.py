import sys, json; sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c9')
import hubgraph as H
from hubgraph import *
import numpy as np
S = [int(x) for x in np.load('spread_ls.npy')]
O = sorted(int(x) for x in np.load('ovoid_ls.npy'))
# add R1 freed points on t1 (points of lvl1 -> lines of lvl2): need slots: remove T1 edges and add B-hub at lvl1 point, A-hub at lvl2 line
def build_full(R0, R2, R1, Bh, Ah, Y):
    """Bh: list of lists of ('a',c),('s',s),('p',p) ; Ah: lists of ('b',c),('t',s),('r',p)"""
    removed = set(T0[c] for c in R0) | set(T2[s] for s in R2) | set(T1[p] for p in R1)
    E = BASE + [e for e in MATCH if e not in removed]
    nv = 3*PER; nB = len(Bh); nA = len(Ah)
    for h, slots in enumerate(Bh):
        for kind, x in slots:
            v = {'a': ALPHA(x), 's': SIGMA(x), 'p': 1*PER + x}[kind]
            E.append((nv+h, v))
    for g, slots in enumerate(Ah):
        for kind, x in slots:
            v = {'b': BETA(x), 't': TAU(x), 'r': 2*PER + NP + x}[kind]
            E.append((nv+nB+g, v))
    for (h, g) in Y: E.append((nv+h, nv+nB+g))
    deg = np.zeros(nv+nB+nA, dtype=int)
    for u, v in E: deg[u]+=1; deg[v]+=1
    newid = {}; k=0
    for v in range(nv+nB+nA):
        if v < nv or deg[v] > 0: newid[v]=k; k+=1
    return k, [(newid[u], newid[v]) for u,v in E]
import random
rng = random.Random(0)
R0 = S + [5]
for trial in range(4):
    p = rng.randrange(NP); c = rng.randrange(NL)
    s = rng.choice(O)
    n, E = build_full(R0, O, [p], [[('a', 5), ('p', p), ('s', s)]], [], [])
    print('R1={p}, B-hub{alpha5,p,sigma_s}:', evaluate(n, E, 'R1'))
n, E = build_full(R0, O, [], [], [], [])
print('no R1, no hubs:', evaluate(n, E, 'R1'))
n, E = build_full(R0, O, [5], [], [], [])
print('R0 with R1 nothing wait', evaluate(n,E,'R1'))
