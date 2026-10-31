#!/usr/bin/env python3
"""SAT search (worker c3) for Z_p voltage lifts of cubic bipartite base multigraphs on k+k vertices, lift diameter <= D.

Variables: E[a,b,t] = base edge a (side 0) -- b (side 1) with voltage t (lift: (a,g) ~ (b,g+t)); at most one per (a,b,t).
Degrees: every base vertex has exactly 3 edges (cardinality encodings).
Reachability: for every source s = (u,0), u on either side, layered walk variables R[j][x] (x = (w,g) a lift vertex, j the
walk length) with witnesses W = R[j][x] & E[e]; R[j+1][x'] -> OR of its witnesses (so R true only with a real walk).
Coverage: every lift vertex x' on the same side as s is reached by a walk of even length 2..D-1.
Walks need not be non-backtracking: a walk of length <= D-1 reduces to a non-backtracking one with the same endpoint.
Since the lift is vertex-transitive under Z_p, the sources (u,0) for all base vertices u suffice.

Usage: sat_lift.py p k D [solver] [seed-unused] [outfile]   -- writes the lifted edge list (vertex (w,g) = w*p+g) if found.
"""
import sys, time
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


SYM = True


def build(p, k, D, pool=None):
    pool = pool or IDPool()
    E = {}
    for a in range(k):
        for b in range(k):
            for t in range(p):
                E[(a, b, t)] = pool.id(('E', a, b, t))
    clauses = []
    for a in range(k):
        lits = [E[(a, b, t)] for b in range(k) for t in range(p)]
        clauses += CardEnc.equals(lits=lits, bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
    for b in range(k):
        lits = [E[(a, b, t)] for a in range(k) for t in range(p)]
        clauses += CardEnc.equals(lits=lits, bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
    # incident edge options per base node: node w < k is side 0, node k+b is side 1
    inc = {}
    for w in range(2 * k):
        inc[w] = []
    for a in range(k):
        for b in range(k):
            for t in range(p):
                inc[a].append((b, t, E[(a, b, t)]))       # from a: to b (node k+b), voltage +t
                inc[k + b].append((a, t, E[(a, b, t)]))   # from b: to a, voltage -t
    # symmetry breaking (valid when base vertex 0 has 3 distinct neighbours): relabel B so N(0) = {0,1,2}, then gauge
    # voltages (potential shifts on B) so that the three edges at base vertex 0 have voltage 0.
    if SYM:
        for b in range(k):
            for t in range(p):
                clauses.append([E[(0, b, t)]] if (b < 3 and t == 0) else [-E[(0, b, t)]])
    L = D - 1
    nsrc_vars = 0
    for src in range(2 * k):
        s_side = 0 if src < k else 1
        R = [dict() for _ in range(L + 1)]
        v0 = pool.id(('R', src, 0, src, 0))
        R[0][(src, 0)] = v0
        clauses.append([v0])
        for j in range(L):
            wit = {}
            for (w, g), rv in R[j].items():
                for (w2, t, ev) in inc[w]:
                    if w < k:
                        x2 = (k + w2, (g + t) % p)
                    else:
                        x2 = (w2, (g - t) % p)
                    Wv = pool.id(('W', src, j, w, g, w2, t))
                    clauses.append([-Wv, rv])
                    clauses.append([-Wv, ev])
                    wit.setdefault(x2, []).append(Wv)
            for x2, ws in wit.items():
                rv2 = pool.id(('R', src, j + 1, x2[0], x2[1]))
                R[j + 1][x2] = rv2
                clauses.append([-rv2] + ws)
        # coverage of same-side lift vertices
        for w in range(2 * k):
            if (w < k) != (src < k):
                continue
            for h in range(p):
                if w == src and h == 0:
                    continue
                lits = []
                for j in range(2, L + 1, 2):
                    if (w, h) in R[j]:
                        lits.append(R[j][(w, h)])
                if not lits:
                    clauses.append([])  # unreachable target: unsatisfiable
                else:
                    clauses.append(lits)
    return clauses, E, pool


def lift_edges(p, k, E, model_set):
    base = [(a, b, t) for (a, b, t), v in E.items() if v in model_set]
    edges = []
    for a, b, t in base:
        for g in range(p):
            edges.append((a * p + g, (k + b) * p + (g + t) % p))
    return base, edges


def far_of(n, edges, D):
    adj = [[] for _ in range(n)]
    for x, y in edges:
        adj[x].append(y); adj[y].append(x)
    far = 0
    for s in range(n):
        dist = [-1] * n; dist[s] = 0; q = [s]
        for x in q:
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1; q.append(y)
        far += sum(1 for i in range(n) if i != s and (dist[i] < 0 or dist[i] > D))
    return far // 2


def main():
    p, k, D = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    sname = sys.argv[4] if len(sys.argv) > 4 else 'cadical195'
    outf = sys.argv[5] if len(sys.argv) > 5 else None
    global SYM
    import os
    SYM = os.environ.get('SYM', '1') == '1'
    t0 = time.time()
    clauses, E, pool = build(p, k, D)
    print(f"built p={p} k={k} D={D} vars={pool.top} clauses={len(clauses)} in {time.time()-t0:.1f}s", flush=True)
    with Solver(name=sname, bootstrap_with=clauses) as S:
        t1 = time.time()
        ok = S.solve()
        print(f"solver {sname}: {'SAT' if ok else 'UNSAT'} in {time.time()-t1:.1f}s", flush=True)
        if ok:
            mset = set(l for l in S.get_model() if l > 0)
            base, edges = lift_edges(p, k, E, mset)
            n = 2 * k * p
            f = far_of(n, edges, D)
            print(f"base edges {len(base)} lift n={n} far={f}", flush=True)
            print("BASE", ' '.join(f"{a}-{b}:{t}" for a, b, t in base), flush=True)
            if outf:
                with open(outf, 'w') as fh:
                    fh.write(f"{n}\n" + ''.join(f"{x} {y}\n" for x, y in edges))


if __name__ == '__main__':
    main()
