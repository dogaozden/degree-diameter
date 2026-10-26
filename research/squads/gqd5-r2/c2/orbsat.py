"""SAT for relaxed sets T on W(11) invariant under a cyclic group C = <g>, g = unipotent [[I,B],[0,I]] with
B = [[x,y],[y,al*x+be*y]] (a symmetry preserving the regular spread S, see syms.py).  Points of each C-orbit are
all in or all out.  Usage: orbsat.py x y k outfile [solver]"""
import sys, json, time
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r2/c2')
import numpy as np, gqlib
from sat_model import build, X, n, plines, lines, S
from verify import verify
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver
G = gqlib.W(11); F = G.F; q = 11
pts = G.coords; index = G.index
al, be = next((a, b) for a in range(q) for b in range(q)
              if all(F.sub[F.sub[F.mul[x][x]][F.mul[b][x]]][a] != 0 for x in range(q)))
def perm_of(M):
    out = []
    for v in pts:
        w = [0, 0, 0, 0]
        for j in range(4):
            acc = 0
            for i in range(4):
                acc = F.add[acc][F.mul[v[i]][M[i][j]]]
            w[j] = acc
        s = next(x for x in w if x); inv = F.inv[s]
        out.append(index[tuple(F.mul[inv][x] for x in w)])
    return out
def unip(x, y, t=1):
    z = F.add[F.mul[al][x]][F.mul[be][y]]
    return perm_of([[1,0,F.mul[t][x],F.mul[t][y]],[0,1,F.mul[t][y],F.mul[t][z]],[0,0,1,0],[0,0,0,1]])
if __name__ == '__main__':
    x, y, k = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]); out = sys.argv[4]
    solver = sys.argv[5] if len(sys.argv) > 5 else 'cd15'
    g = unip(x, y)
    col = G.col
    assert np.array_equal(col[np.ix_(g, g)], col), 'not an automorphism'
    t0 = time.time()
    cnf, top = build()
    cnf_clauses = list(cnf.clauses)
    for p in range(n):
        a, b = X(p), X(g[p])
        cnf_clauses.append([-a, b]); cnf_clauses.append([a, -b])
    card = CardEnc.atleast([X(p) for p in range(n)], k, top_id=top, encoding=EncType.seqcounter)
    cnf_clauses += card.clauses
    orb = {}
    seen = set(); orbits = []
    for p in range(n):
        if p in seen: continue
        o = [p]; seen.add(p); r = g[p]
        while r != p: o.append(r); seen.add(r); r = g[r]
        orbits.append(o)
    print('orbits', len(orbits), 'sizes', sorted(set(len(o) for o in orbits)), 'build', round(time.time()-t0,1), flush=True)
    with Solver(name=solver, bootstrap_with=cnf_clauses) as s:
        ok = s.solve()
        print('x,y', x, y, 'k', k, 'SAT' if ok else 'UNSAT', 'time', round(time.time()-t0,1), flush=True)
        if ok:
            m = s.get_model()
            T = [p for p in range(n) if m[X(p)-1] > 0]
            print(verify(T), flush=True)
            json.dump(sorted(T), open(out, 'w'))
