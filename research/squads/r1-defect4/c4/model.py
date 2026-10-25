#!/usr/bin/env python3
"""Card c4 (squad r1-defect4): CP-SAT model for a bipartite (k,3,-4)-graph, k >= 5 (then k-regular, n = k^2-k-1).

Strategy: constraint programming (OR-Tools CP-SAT, one worker, symmetry detection on) instead of plain CNF.

Model: X[p][l] in {0,1} is the point-line incidence matrix (n x n).
  * row sums and column sums equal k;
  * for every pair of points u<v, the common-line count c[u][v] = sum_l (X[u][l] AND X[v][l]) is >= 1;
  * for every pair of lines l<m, the common-point count d[l][m] = sum_p (X[p][l] AND X[p][m]) is >= 1.
    (Diameter 3 of the bipartite incidence graph <=> these two pair conditions, given k-regularity.)

Normal form (same as research/projects/optimal-sat/defect4/enc_d3m4.py, sound: relabel lines so that the lines
through point 0 are 0..k-1, then relabel points so that the points on line 0 are 0..k-1; point 0 stays on lines 0..k-1):
  point 0 is on lines 0..k-1, line 0 contains points 0..k-1.

Redundant but implied constraints (proved consequences, kept only to help propagation; flag --plain drops them):
  Fix a point u. Each line through u has k-1 other points, so sum_{v!=u} c[u][v] = k(k-1) (exact count, since
  c[u][v] is the exact number of common lines). Every v != u has c[u][v] >= 1, so sum_{v!=u} (c[u][v]-1) = k(k-1)-(n-1) = 2.
  Hence 1 <= c[u][v] <= 3. The same holds for lines with d[l][m].
  Exactness: z[u,v,l] <-> X[u][l] AND X[v][l] is an equivalence, so c[u][v] really counts common lines.

usage: model.py k [--time S] [--sym L] [--plain] [--workers W] [--log] [--solution out.txt]
  exit 0 = solved (SAT or UNSAT), prints a status line with wall time; SAT answers are verified independently
  (2n-vertex bipartite graph, k-regular, diameter 3, with networkx).
"""
import sys, time, argparse, itertools
from ortools.sat.python import cp_model


def build(k, redundant=True):
    n = k * k - k - 1
    m = cp_model.CpModel()
    X = [[m.NewBoolVar(f'x_{p}_{l}') for l in range(n)] for p in range(n)]

    # normal form (sound, see module docstring)
    for l in range(n):
        m.Add(X[0][l] == (1 if l < k else 0))
    for p in range(n):
        m.Add(X[p][0] == (1 if p < k else 0))

    # k-regularity on both sides (k >= 5 and the (k,3,-4) definition)
    for p in range(n):
        m.Add(sum(X[p]) == k)
    for l in range(n):
        m.Add(sum(X[p][l] for p in range(n)) == k)

    # Point pairs: exact common-line count c[u][v] >= 1.  Lines pairs: exact common-point count d[l][m] >= 1.
    # side 0: points, the "shared" index is a line l; side 1: lines, the shared index is a point p.
    for side in (0, 1):
        def E(a, b, t):  # incidence of point/line pair (a,b) at the shared index t
            return X[a][t] if side == 0 else X[t][a]
        size = n
        cnt = {}
        for a, b in itertools.combinations(range(size), 2):
            zs = []
            for t in range(n):
                z = m.NewBoolVar('')
                ea, eb = E(a, b, t), E(b, a, t)
                # exact: z <-> ea AND eb
                m.AddImplication(z, ea)
                m.AddImplication(z, eb)
                m.AddBoolOr([ea.Not(), eb.Not(), z])
                zs.append(z)
            c = sum(zs)
            m.AddBoolOr(zs)            # diameter-3 pair condition: at least one common line/point
            cnt[a, b] = c
            if redundant:
                m.Add(c <= 3)          # implied: sum over v != u of (c-1) equals 2
        if redundant:
            for u in range(size):
                m.Add(sum(cnt[min(u, v), max(u, v)] for v in range(size) if v != u) == k * (k - 1))
    return m, X, n


def verify(k, grid):
    """Independent check: incidence matrix -> bipartite graph; k-regular and diameter exactly 3 (and <= 3)."""
    import networkx as nx
    n = len(grid)
    G = nx.Graph()
    G.add_nodes_from([('P', p) for p in range(n)] + [('L', l) for l in range(n)])
    for p in range(n):
        for l in range(n):
            if grid[p][l]:
                G.add_edge(('P', p), ('L', l))
    degs = {d for _, d in G.degree()}
    diam = nx.diameter(G)
    return degs == {k} and diam <= 3, degs, diam


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('k', type=int)
    ap.add_argument('--time', type=float, default=900.0)
    ap.add_argument('--sym', type=int, default=4, help='CP-SAT symmetry_level (2 default, 4 = aggressive)')
    ap.add_argument('--workers', type=int, default=1)
    ap.add_argument('--plain', action='store_true', help='without the redundant implied constraints')
    ap.add_argument('--log', action='store_true')
    ap.add_argument('--lin', type=int, default=None, help='CP-SAT linearization_level (0 = pure SAT-like)')
    ap.add_argument('--seed', type=int, default=None)
    ap.add_argument('--solution', default=None)
    a = ap.parse_args()

    t0 = time.time()
    m, X, n = build(a.k, redundant=not a.plain)
    t_build = time.time() - t0

    s = cp_model.CpSolver()
    s.parameters.num_workers = a.workers          # one worker, as the squad rules require
    s.parameters.symmetry_level = a.sym           # symmetry detection on
    s.parameters.max_time_in_seconds = a.time
    s.parameters.log_search_progress = a.log
    if a.lin is not None:
        s.parameters.linearization_level = a.lin
    if a.seed is not None:
        s.parameters.random_seed = a.seed
    t1 = time.time()
    st = s.Solve(m)
    t_solve = time.time() - t1
    name = s.StatusName(st)

    ok = None
    if name in ('OPTIMAL', 'FEASIBLE'):
        grid = [[s.Value(X[p][l]) for l in range(n)] for p in range(n)]
        ok, degs, diam = verify(a.k, grid)
        if a.solution:
            with open(a.solution, 'w') as f:
                for row in grid:
                    f.write(''.join(map(str, row)) + '\n')
        print(f'k={a.k} n={n} SAT verified={ok} degs={sorted(degs)} diam={diam}')
    elif name == 'INFEASIBLE':
        print(f'k={a.k} n={n} UNSAT')
    else:
        print(f'k={a.k} n={n} {name} (no answer)')
    print(f'k={a.k} build={t_build:.2f}s solve={t_solve:.2f}s wall={time.time()-t0:.2f}s '
          f'status={name} sym={a.sym} lin={a.lin} workers={a.workers} redundant={not a.plain} '
          f'conflicts={s.NumConflicts()} branches={s.NumBranches()}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
