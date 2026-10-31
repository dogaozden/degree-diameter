"""Multi-generator version of mkgroup.py. Writes a group file and a G-invariant degree-only start graph for symloc/symloc2.
usage: mkgroup2.py M K SEED GROUPFILE GRAPHFILE GEN [GEN ...]
  GEN = ALPHA:SIGA:SIGB  (SIGA/SIGB = cycle lengths of sigma on the K base vertices of A / B, e.g. 4,4,4,4,1; use '-'
  for the identity). Generator (u,h) -> (sigma u, alpha h) on lift vertices (u,h) = u*M+h; A = u<K, B = K..2K-1.
  The free shift z(u,h) = (u,h+1) is always included. Every GEN must satisfy: E[a,b,t] = E[sigma a, sigma b, alpha t].
"""
import sys, random
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
m, k, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
gf, grf = sys.argv[4], sys.argv[5]
gens_spec = sys.argv[6:]
rng = random.Random(seed)
def perm_from_cycles(s):
    if s.strip() == '-': return list(range(k))
    lens = [int(x) for x in s.split(',') if x.strip()]
    assert sum(lens) == k, (s, k)
    perm = list(range(k)); pos = 0
    for L in lens:
        c = list(range(pos, pos + L))
        for i, x in enumerate(c): perm[x] = c[(i + 1) % L]
        pos += L
    return perm
n = 2 * k * m
def vid(u, h): return u * m + (h % m)
gens_perm = [[vid(u // m, (u % m) + 1) for u in range(n)]]   # z
specs = []
for g in gens_spec:
    al, sa, sb = g.split(':')
    al = int(al) % m; pA = perm_from_cycles(sa); pB = perm_from_cycles(sb)
    sig = pA + [k + x for x in pB]
    specs.append((al, pA, pB))
    gens_perm.append([vid(sig[u // m], al * (u % m)) for u in range(n)])
ident = tuple(range(n)); G = {ident}; frontier = [ident]
while frontier:
    new = []
    for p in frontier:
        for g in gens_perm:
            q = tuple(g[p[x]] for x in range(n))
            if q not in G: G.add(q); new.append(q)
    frontier = new
G = sorted(G)
if len(G) > 64: print('group too big', len(G)); sys.exit(2)
with open(gf, 'w') as f:
    f.write('%d %d\n' % (n, len(G)))
    for p in G: f.write(' '.join(map(str, p)) + '\n')
    f.write(' '.join('0' if v // m < k else '1' for v in range(n)) + '\n')
print('group order', len(G))
pool = IDPool(); E = {}
for a in range(k):
    for b in range(k):
        for t in range(m): E[(a, b, t)] = pool.id(('E', a, b, t))
cl = []
for al, pA, pB in specs:
    for (a, b, t), v in E.items():
        y = E[(pA[a], pB[b], (al * t) % m)]
        if v != y: cl += [[-v, y], [v, -y]]
for a in range(k):
    cl += CardEnc.equals([E[(a, b, t)] for b in range(k) for t in range(m)], bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
for b in range(k):
    cl += CardEnc.equals([E[(a, b, t)] for a in range(k) for t in range(m)], bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
rng.shuffle(cl)
with Solver(name='cadical195', bootstrap_with=cl) as S:
    if not S.solve():
        print('UNSAT start'); sys.exit(3)
    mod = set(l for l in S.get_model() if l > 0)
edges = []
for (a, b, t), v in E.items():
    if v in mod:
        for h in range(m): edges.append((vid(a, h), vid(k + b, h + t)))
with open(grf, 'w') as f:
    f.write('%d\n' % n)
    for x, y in edges: f.write('%d %d\n' % (x, y))
print('start graph edges', len(edges), 'n', n)
