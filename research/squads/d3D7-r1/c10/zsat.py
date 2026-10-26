#!/usr/bin/env python3
"""SAT search for cubic bipartite diameter-D lifts over Z_N of a p+p base.

Base: bipartite multigraph on A = {0..p-1}, B = {p..2p-1}; base edge (u, j, a) for u in A, j in 0..p-1, a in Z_N
(multi-edges allowed when voltages differ). Lift: vertex (w, g) = w*N+g; edge (u,g)~(p+j,(g+a)%N).
Every base vertex has exactly 3 incident base edges -> lift is simple cubic bipartite on 2pN vertices.

Reachability (diameter D = 7 means same-side distance <= 6, see BRIEF):
  E[s][x][t] = "there is a walk of length exactly t from source (s,0) to lifted vertex x", defined only when t has the
  parity of the side difference. E[s][(s,0)][0] is true. E[s][x][t] -> OR over neighbours y of (edge literal AND E[s][y][t-1]).
  Soundness: true E implies a real walk. For every same-side x != (s,0): OR_{t even, 2<=t<=R} E[s][x][t] with R = 6.
Sources s = all 2p base vertices (translation by Z_N covers all lifted sources).
"""
import sys, time, subprocess, argparse, os
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

ap = argparse.ArgumentParser()
ap.add_argument('p', type=int)
ap.add_argument('N', type=int)
ap.add_argument('--R', type=int, default=6, help='max same-side distance (diameter 7 -> 6)')
ap.add_argument('--solver', default='cadical195')
ap.add_argument('--out', default='')
ap.add_argument('--base', default='', help='fix the base multigraph (liftx format: header V E, then u v edges)')
args = ap.parse_args()
p, N, R = args.p, args.N, args.R
n = 2 * p * N
HERE = os.path.dirname(os.path.abspath(__file__))
APSP = '/home/user/degree-diameter/research/d3D7/bin/apsp'

top = [0]
def new():
    top[0] += 1
    return top[0]

S = Solver(name=args.solver)
nclauses = [0]
def add(cl):
    nclauses[0] += 1
    S.add_clause(cl)

def add_card_equals(lits, k):
    cnf = CardEnc.equals(lits=lits, bound=k, top_id=top[0], encoding=EncType.seqcounter)
    top[0] = max(top[0], cnf.nv)
    for cl in cnf.clauses:
        add(cl)

# edge variables e[(u,j,a)]
e = {}
for u in range(p):
    for j in range(p):
        for a in range(N):
            e[(u, j, a)] = new()

def inc_lits(w):
    if w < p:
        return [e[(w, j, a)] for j in range(p) for a in range(N)]
    j = w - p
    return [e[(u, j, a)] for u in range(p) for a in range(N)]

def nbrs(x):
    """list of (edge literal, neighbour lifted vertex id)"""
    w, g = divmod(x, N)
    out = []
    if w < p:
        u = w
        for j in range(p):
            for a in range(N):
                out.append((e[(u, j, a)], (p + j) * N + (g + a) % N))
    else:
        j = w - p
        for u in range(p):
            for a in range(N):
                out.append((e[(u, j, a)], u * N + (g - a) % N))
    return out

def side(w):
    return 0 if w < p else 1

if args.base:
    mult = {}
    with open(args.base) as f:
        hdr = f.readline()
        for line in f:
            if line.strip():
                u, v = map(int, line.split())
                if u > v: u, v = v, u
                mult[(u, v - p)] = mult.get((u, v - p), 0) + 1
    for (u, j), m in mult.items():
        add_card_equals([e[(u, j, a)] for a in range(N)], m)
    for (u, j, a), v in list(e.items()):
        if (u, j) not in mult:
            add([-v])
    print('fixed base', args.base, 'pairs', len(mult), 'multiplicities', sorted(mult.values()), flush=True)

# degree: every base vertex has exactly 3 incident base edges
for w in range(2 * p):
    add_card_equals(inc_lits(w), 3)

# symmetry break: some edge at A0 has voltage 0 (shift the B fibre)
add([e[(0, j, 0)] for j in range(p)])

# reachability
def side_of_vertex(x):
    return side(x // N)

Evar = {}
for s in range(2 * p):
    src = s * N + 0
    ss = side(s)
    for x in range(2 * p * N):
        par = 0 if side_of_vertex(x) == ss else 1
        for t in range(1, R + 1):
            if t % 2 != par:
                continue
            Evar[(s, x, t)] = new()

def E(s, x, t):
    """literal, True (constant), or None (false)"""
    if t == 0:
        return True if x == s * N else None
    return Evar.get((s, x, t))

for (s, x, t), var in Evar.items():
    cands = []
    for lit, y in nbrs(x):
        ey = E(s, y, t - 1)
        if ey is None:
            continue
        if ey is True:
            cands.append(lit)
        else:
            z = new()
            add([-z, lit])
            add([-z, ey])
            cands.append(z)
    add([-var] + cands)

# targets: same side as source, not the source itself
for s in range(2 * p):
    ss = side(s)
    for x in range(2 * p * N):
        if side_of_vertex(x) != ss or x == s * N:
            continue
        lits = []
        for t in range(2, R + 1, 2):
            v = E(s, x, t)
            if v is not None and v is not True:
                lits.append(v)
        if not lits:
            print('UNSAT trivially: no target lits', s, x, flush=True)
            sys.exit(0)
        add(lits)

print(f'p={p} N={N} n={n} R={R} vars={top[0]} clauses={nclauses[0]}', flush=True)
t0 = time.time()
ok = S.solve()
dt = time.time() - t0
print(f'solve result={ok} time={dt:.1f}s', flush=True)
if ok:
    m = set(l for l in S.get_model() if l > 0)
    edges = []
    for (u, j, a), v in e.items():
        if v in m:
            for g in range(N):
                edges.append((u * N + g, (p + j) * N + (g + a) % N))
    out = args.out or os.path.join(HERE, f'sol_p{p}_N{N}_n{n}.edges')
    with open(out, 'w') as f:
        f.write(f'{n}\n')
        for a_, b_ in edges:
            f.write(f'{a_} {b_}\n')
    print('wrote', out, 'edges', len(edges), flush=True)
    r = subprocess.run([APSP, out, '3', '7'], capture_output=True, text=True)
    print(r.stdout.strip().splitlines()[-1] if r.stdout.strip() else r.stderr, flush=True)
