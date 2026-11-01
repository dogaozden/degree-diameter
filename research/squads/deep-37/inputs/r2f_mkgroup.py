"""Write a group file and a G-invariant start graph for symloc.c.
usage: mkgroup.py M K ALPHA SIGMA_A_CYCLES SIGMA_B_CYCLES GROUPFILE GRAPHFILE [seed]
G = <z, s>: z(u,h) = (u,h+1), s(u,h) = (sigma u, alpha h) (lift vertices (u,h) = u*M+h, A = u < K, B = K..2K-1).
Start graph: degree-only SAT (random clause order) with the same E-symmetry; no reachability constraints."""
import sys, random, itertools
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
m, k, alpha = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]) % int(sys.argv[1])
cA, cB, gf, grf = sys.argv[4], sys.argv[5], sys.argv[6], sys.argv[7]
seed = int(sys.argv[8]) if len(sys.argv) > 8 else 1
rng = random.Random(seed)
def perm_from_cycles(s, off):
    lens = [int(x) for x in s.split(',') if x.strip()]
    perm = []; pos = 0; cycles = []
    for L in lens:
        cycles.append(list(range(pos, pos + L))); pos += L
    perm = list(range(pos))
    for c in cycles:
        for i, x in enumerate(c): perm[x] = c[(i + 1) % len(c)]
    assert pos == k, (pos, k)
    return perm
pA = perm_from_cycles(cA, 0); pB = perm_from_cycles(cB, 0)
sig = [pA[i] for i in range(k)] + [k + pB[i] for i in range(k)]
n = 2 * k * m
def vid(u, h): return u * m + (h % m)
# group closure as permutations of lift vertices
gens = []
gens.append([vid(u // m, (u % m) + 1) for u in range(n)])
gens.append([vid(sig[u // m], alpha * (u % m)) for u in range(n)])
ident = tuple(range(n))
G = {ident}; frontier = [ident]
while frontier:
    new = []
    for p in frontier:
        for g in gens:
            q = tuple(g[p[x]] for x in range(n))
            if q not in G:
                G.add(q); new.append(q)
    frontier = new
G = sorted(G)
with open(gf, 'w') as f:
    f.write('%d %d\n' % (n, len(G)))
    for p in G: f.write(' '.join(map(str, p)) + '\n')
    f.write(' '.join('0' if v // m < k else '1' for v in range(n)) + '\n')
print('group order', len(G))
# start graph by SAT on base degrees with E-symmetry
pool = IDPool(); E = {}
for a in range(k):
    for b in range(k):
        for t in range(m): E[(a, b, t)] = pool.id(('E', a, b, t))
cl = []
for (a, b, t), v in E.items():
    y = E[(pA[a], pB[b], (alpha * t) % m)]
    if v != y: cl += [[-v, y], [v, -y]]
for a in range(k):
    cl += CardEnc.equals([E[(a, b, t)] for b in range(k) for t in range(m)], bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
for b in range(k):
    cl += CardEnc.equals([E[(a, b, t)] for a in range(k) for t in range(m)], bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
rng.shuffle(cl)
with Solver(name='cadical195', bootstrap_with=cl) as S:
    ok = S.solve()
    assert ok
    mod = set(l for l in S.get_model() if l > 0)
edges = []
for (a, b, t), v in E.items():
    if v in mod:
        for h in range(m):
            edges.append((vid(a, h), vid(k + b, h + t)))
with open(grf, 'w') as f:
    f.write('%d\n' % n)
    for x, y in edges: f.write('%d %d\n' % (x, y))
print('start graph edges', len(edges), 'n', n)
