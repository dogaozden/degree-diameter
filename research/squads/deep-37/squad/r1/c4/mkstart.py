"""mkstart.py GROUPFILE GRAPHFILE [seed]: a G-invariant cubic bipartite start graph for any group file (orbit-level SAT).
Variables = edge orbits (unordered cross-colour pairs under G). Degree 3 at one representative per vertex orbit.
Duplicate incidences of one edge orbit at a vertex are handled with equivalence auxiliaries."""
import sys, random
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
gf, grf = sys.argv[1], sys.argv[2]
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
rng = random.Random(seed)
with open(gf) as f:
    n, order = map(int, f.readline().split())
    G = [list(map(int, f.readline().split())) for _ in range(order)]
    col = list(map(int, f.readline().split()))
# vertex orbits
orb = [-1] * n; reps = []
for v in range(n):
    if orb[v] < 0:
        reps.append(v)
        for g in G: orb[g[v]] = v
# edge orbits
eorb = {}; orbs = []
for u in range(n):
    for v in range(u + 1, n):
        if col[u] == col[v] or (u, v) in eorb: continue
        members = set()
        for g in G:
            a, b = g[u], g[v]
            members.add((a, b) if a < b else (b, a))
        idx = len(orbs); orbs.append(sorted(members))
        for p in members: eorb[p] = idx
print('group order', order, 'vertex orbits', len(reps), 'edge orbits', len(orbs), file=sys.stderr)
pool = IDPool()
X = [pool.id(('x', i)) for i in range(len(orbs))]
cl = []
for r in reps:
    inc = {}
    for (a, b) in [p for p in eorb if r in p]:
        k = eorb[(a, b)]
        inc[k] = inc.get(k, 0) + 1
    lits = []
    for k, c in inc.items():
        lits.append(X[k])
        for t in range(c - 1):
            y = pool.id(('dup', r, k, t))
            cl += [[-y, X[k]], [y, -X[k]]]
            lits.append(y)
    cnf = CardEnc.equals(lits=lits, bound=3, vpool=pool, encoding=EncType.seqcounter)
    cl += cnf.clauses
    # nothing else
rng.shuffle(cl)
with Solver(name='cadical195', bootstrap_with=cl) as S:
    if not S.solve():
        print('UNSAT: no G-invariant cubic start', file=sys.stderr); sys.exit(2)
    mod = set(l for l in S.get_model() if l > 0)
edges = []
for i, k in enumerate(orbs):
    if X[i] in mod: edges += k
with open(grf, 'w') as f:
    f.write('%d\n' % n)
    for a, b in edges: f.write('%d %d\n' % (a, b))
print('start edges', len(edges), 'cubic check', all(sum(1 for e in edges if x in e) == 3 for x in range(n)), file=sys.stderr)
