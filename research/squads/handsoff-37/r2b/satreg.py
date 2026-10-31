#!/usr/bin/env python3
"""satreg.py (r2b): exact SAT re-solve of a region of a cubic bipartite graph, goal far <= T.

Region S = union of balls (radius RAD) around the given centres. All edges inside S are removed (set R);
the graph F = G - R is fixed outside. Every vertex v in S gets f_v = (number of removed edges at v) new
edges, which go to the opposite side inside S. Variables x_ab (a in S on side 0, b in S on side 1).
Degree constraints: exact cardinality. Distance: for every same-side pair (u,w) we encode
W6(u,w) = "walk of length <= 6 from u to w" by DP over lengths 1..6 (constant-folded through F),
and require that at most T same-side pairs violate W6 (far pairs at distance >= 8).
For a bipartite cubic graph, far(score37) = number of same-side violations when there are no
opposite-side violations; the output is verified with bin/score37 anyway.

Usage: satreg.py IN.edges RAD T SOLVER OUT.edges centre1 [centre2 ...]
  prints SAT/UNSAT, timings and the encoding size. On SAT writes OUT.edges.
"""
import sys
import threading
import time
from collections import deque

from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def load(fn):
    with open(fn) as f:
        toks = f.read().split()
    n = int(toks[0])
    e = [(int(toks[i]), int(toks[i + 1])) for i in range(1, len(toks), 2)]
    adj = [[] for _ in range(n)]
    for a, b in e:
        adj[a].append(b)
        adj[b].append(a)
    return n, adj


def bfs(adjs, s):
    d = [-1] * len(adjs)
    d[s] = 0
    q = deque([s])
    while q:
        x = q.popleft()
        for y in adjs[x]:
            if d[y] < 0:
                d[y] = d[x] + 1
                q.append(y)
    return d


class Enc:
    def __init__(self):
        self.nv = 0
        self.clauses = []

    def new(self):
        self.nv += 1
        return self.nv

    def OR(self, lits):
        out = []
        for l in lits:
            if l is True:
                return True
            if l is False:
                continue
            out.append(l)
        out = list(set(out))
        if not out:
            return False
        if len(out) == 1:
            return out[0]
        v = self.new()
        for l in out:
            self.clauses.append([-l, v])
        self.clauses.append([-v] + out)
        return v

    def AND(self, lits):
        out = []
        for l in lits:
            if l is False:
                return False
            if l is True:
                continue
            out.append(l)
        out = list(set(out))
        if not out:
            return True
        if len(out) == 1:
            return out[0]
        v = self.new()
        for l in out:
            self.clauses.append([-v, l])
        self.clauses.append([v] + [-l for l in out])
        return v


def region_of(n, adj, centres, rad):
    S = set()
    for c in centres:
        d = bfs(adj, c)
        for v in range(n):
            if 0 <= d[v] <= rad:
                S.add(v)
    return sorted(S)


def build_and_solve(n, adj, col, S, T, solver_name, verbose=True, tlim=None, forbid=None):
    """forbid: list of (a, b) region pairs (a on side 0) whose new-edge variable is assumed false
    (diversifies plateau moves: the solution must avoid these pairs)."""
    t0 = time.time()
    Sset = set(S)
    Rset = set()
    for v in S:
        for w in adj[v]:
            if w in Sset and v < w:
                Rset.add((v, w))
    Fadj = [[] for _ in range(n)]
    for v in range(n):
        for w in adj[v]:
            if (min(v, w), max(v, w)) not in Rset:
                Fadj[v].append(w)
    f = {v: 3 - len(Fadj[v]) for v in S}
    A = [v for v in S if col[v] == 0]
    B = [v for v in S if col[v] == 1]
    enc = Enc()
    x = {}
    for a in A:
        for b in B:
            x[(a, b)] = enc.new()
    cand = [[] for _ in range(n)]
    for (a, b), lit in x.items():
        cand[a].append((b, lit))
        cand[b].append((a, lit))
    # degree constraints (exact)
    for a in A:
        lits = [x[(a, b)] for b in B]
        if f[a] > len(lits):
            return None, "infeasible degree"
        cnf = CardEnc.equals(lits=lits, bound=f[a], top_id=enc.nv, encoding=EncType.seqcounter)
        enc.nv = max(enc.nv, cnf.nv)
        enc.clauses.extend(cnf.clauses)
    for b in B:
        lits = [x[(a, b)] for a in A]
        if f[b] > len(lits):
            return None, "infeasible degree"
        cnf = CardEnc.equals(lits=lits, bound=f[b], top_id=enc.nv, encoding=EncType.seqcounter)
        enc.nv = max(enc.nv, cnf.nv)
        enc.clauses.extend(cnf.clauses)
    dF = [bfs(Fadj, u) for u in range(n)]
    viol = []
    constviol = 0
    for u in range(n):
        Wprev = [False] * n
        Wprev[u] = True
        du = dF[u]
        for k in range(1, 7):
            Wcur = [False] * n
            for z in range(n):
                if z == u:
                    Wcur[z] = True
                    continue
                if 0 <= du[z] <= k:
                    Wcur[z] = True
                    continue
                terms = [Wprev[z]]
                for y in Fadj[z]:
                    terms.append(Wprev[y])
                for (y, lit) in cand[z]:
                    terms.append(enc.AND([Wprev[y], lit]))
                Wcur[z] = enc.OR(terms)
            Wprev = Wcur
        for w in range(u + 1, n):
            if col[w] != col[u]:
                continue
            if 0 <= du[w] <= 6:
                continue
            lit = Wprev[w]
            if lit is True:
                continue
            if lit is False:
                constviol += 1
                continue
            viol.append(-lit)
    t_enc = time.time() - t0
    bound = T - constviol
    if verbose:
        print(f"region |S|={len(S)} K={len(Rset)} vars={x and len(x)} aux={enc.nv} clauses={len(enc.clauses)} "
              f"violvars={len(viol)} constviol={constviol} bound={bound} enc={t_enc:.1f}s", flush=True)
    if bound < 0:
        return False, None
    if viol:
        card = CardEnc.atmost(lits=viol, bound=bound, top_id=enc.nv, encoding=EncType.seqcounter)
        enc.nv = max(enc.nv, card.nv)
        enc.clauses.extend(card.clauses)
    t1 = time.time()
    assum = [-x[p] for p in (forbid or []) if p in x]
    with Solver(name=solver_name, bootstrap_with=enc.clauses) as s:
        if tlim:
            timer = threading.Timer(tlim, s.interrupt)
            timer.start()
            ok = s.solve_limited(assumptions=assum, expect_interrupt=True)
            timer.cancel()
            if ok is None:
                if verbose:
                    print(f"solver {solver_name}: TIMEOUT after {tlim}s", flush=True)
                return None, None
        else:
            ok = s.solve(assumptions=assum)
        t_solve = time.time() - t1
        if verbose:
            print(f"solver {solver_name}: {'SAT' if ok else 'UNSAT'} in {t_solve:.1f}s", flush=True)
        if not ok:
            return False, None
        model = s.get_model()
    ms = set(l for l in model if l > 0)
    newedges = [(a, b) for (a, b), lit in x.items() if lit in ms]
    edges = []
    for v in range(n):
        for w in Fadj[v]:
            if v < w:
                edges.append((v, w))
    edges += newedges
    return True, edges


def main():
    fn, rad, T, solver_name, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], sys.argv[5]
    centres = [int(c) for c in sys.argv[6:]]
    n, adj = load(fn)
    col = [c % 2 for c in bfs(adj, 0)]
    S = region_of(n, adj, centres, rad)
    ok, edges = build_and_solve(n, adj, col, S, T, solver_name)
    if ok:
        with open(out, "w") as f:
            f.write(f"{n}\n")
            for a, b in edges:
                f.write(f"{a} {b}\n")
        print("WROTE", out, "edges", len(edges))
    else:
        print("NO SOLUTION" if ok is False else "NONE")


if __name__ == "__main__":
    main()
