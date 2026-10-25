# analysis helper (card c8): cross-class conflict structure for the Hermitian-spread partition of the lines
import sys, collections
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
N, L = len(coord), len(lines)
Q1 = q + 1
pl = [[] for _ in range(N)]
for l in range(L):
    for p in lines[l]:
        pl[p].append(l)
sp = [l for l in range(L) if all(((coord[p][0] + coord[p][4]) % q) == 0 for p in lines[l])]
spset = set(sp)
cls = {}
slot = {}
for m in sp:
    for k, x in enumerate(lines[m]):
        for l in pl[x]:
            if l != m:
                assert l not in cls, 'line meets two spread lines'
                cls[l] = m
                slot[l] = (k, x)
print('spread', len(sp), 'classified', len(cls), 'expected', len(sp) * 132, file=sys.stderr)
def ball4(l):
    out = []
    for p in lines[l]:
        for M in pl[p]:
            if M == l: continue
            out.append(M)
            for r in lines[M]:
                if r == p: continue
                for Nn in pl[r]:
                    if Nn != M: out.append(Nn)
    return out
rng = np.random.default_rng(1)
m0 = sp[0]
C0 = [l for l in cls if cls[l] == m0]
for l in [C0[0], C0[50], C0[100]]:
    b = ball4(l)
    cc = collections.Counter(cls[x] for x in b if x in cls)
    spc = sum(1 for x in b if x in spset)
    vals = collections.Counter(cc.values())
    print('line', l, 'ball', len(b), 'own class', cc.get(cls[l], 0), 'spread in ball', spc,
          'other classes hit', len(cc) - (1 if cls[l] in cc else 0), 'per-class count distribution', dict(vals))
    # is the conflict count per class constant?

# structure of the conflict bipartite graph between two classes
def pair_structure(m, m2):
    A = [l for l in cls if cls[l] == m]
    B2 = set(l for l in cls if cls[l] == m2)
    adj = {}
    for l in A:
        adj[l] = set(x for x in ball4(l) if x in B2)
    degs = collections.Counter(len(adj[l]) for l in A)
    # neighbourhood equivalence classes on the A side
    nbh = collections.Counter(frozenset(adj[l]) for l in A)
    # connected components of the bipartite graph
    par = {}
    def f(a):
        while par.setdefault(a, a) != a:
            par[a] = par[par[a]]; a = par[a]
        return a
    for l in A:
        for x in adj[l]:
            par[f(('a', l))] = f(('b', x))
    comps = collections.Counter(f(('a', l)) for l in A)
    print('pair', m, m2, 'A-degree dist', dict(degs), 'distinct nbhds', len(nbh),
          'nbhd sizes', sorted(collections.Counter(len(k) for k in nbh.elements()).items()) if False else sorted(collections.Counter(len(k) for k in nbh.keys()).items()),
          'components', len(set(f(('a', l)) for l in A)))
    # check whether lines with the same point slot in m behave alike
    return adj
for m2 in [sp[1], sp[2], sp[7]]:
    pair_structure(m0, m2)
