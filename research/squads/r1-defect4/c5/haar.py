#!/usr/bin/env python3
"""Haar-graph search for bipartite (k,3,-4)-graphs (card c5, squad r1-defect4).

Construction. For a group G of order n = k^2-k-1 and S subset of G with |S| = k, the Haar graph H(G,S) has
point set G and line set G, and point g lies on line h iff h - g in S. It is bipartite and k-regular on 2n vertices.

Lemma (drives the search; the final verdict is always re-checked from the explicit graph by verify()):
  H(G,S) has diameter 3  <=>  S - S covers G \\ {0}.
  Proof: distinct points g, g' share a line h iff h = g+s = g'+s' for some s,s' in S, i.e. g-g' = s'-s. Distinct
  lines share a point under the same condition (h-h' = s-s'). A point g off a line h is at distance 3 from h via any
  point g' on h (g, g' are distinct, so they share a line). Distinct points are at even distance in a bipartite graph,
  so distance <= 3 forces distance 2, i.e. the covering condition.
  Counting: the k(k-1) ordered differences of S cover the n-1 nonzero elements iff the over-cover
  sum_{d != 0} max(c(d)-1, 0) equals 2, where c(d) is the number of ordered pairs (s,s') with s-s' = d. Over-cover
  never decreases when S grows, so "over-cover <= 2" is a sound pruning rule for backtracking.

Symmetry. Translating S by t gives an isomorphic Haar graph, so WLOG 0 in S. For odd squarefree n the only abelian
group of order n is cyclic (main() checks squarefreeness), so G = Z_n. n = k^2-k-1 is always odd.

Methods.
  bt_search: exhaustive backtracking over S = {0} u T with over-cover pruning (complete, counts all solutions).
  sat_search: complete SAT encoding (CaDiCaL via pysat). x_g = [g in S]; y_{g,d} = [g in S and g+d in S];
              for every d in 1..(n-1)/2: OR_g y_{g,d} (d in S-S iff -d in S-S, so only half the nonzero d are needed);
              sum_g x_g = k; x_0 = 1 (translation). Sound and complete.
"""
import argparse
import time
from collections import deque


def factorize(n):
    f, d = {}, 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f


def haar_graph(n, S):
    """Adjacency lists: points 0..n-1, lines n..2n-1; point g ~ line n+h iff (h-g) mod n in S."""
    adj = [[] for _ in range(2 * n)]
    for g in range(n):
        for s in S:
            h = (g + s) % n
            adj[g].append(n + h)
            adj[n + h].append(g)
    return adj


def verify(n, k, S):
    """Independent check on the explicit 2n-vertex graph. Uses no difference-set theory.
    Returns (ok, message, common-neighbour histogram over point pairs)."""
    if n != k * k - k - 1:
        return False, "wrong order", None
    if len(set(S)) != k:
        return False, "|S| != k", None
    adj = haar_graph(n, S)
    for v in range(2 * n):
        if len(adj[v]) != k or len(set(adj[v])) != k:
            return False, "not simple k-regular", None
        for u in adj[v]:
            if (u < n) == (v < n):
                return False, "not bipartite", None
    # all pairwise common neighbours, points and lines
    hist = {}
    for side in (range(n), range(n, 2 * n)):
        nb = {v: set(adj[v]) for v in side}
        for u in side:
            for v in side:
                if u < v:
                    c = len(nb[u] & nb[v])
                    if c == 0:
                        return False, f"no common neighbour for pair {u},{v}", None
                    if side.start == 0:
                        hist[c] = hist.get(c, 0) + 1
    # all-pairs BFS diameter
    diam = 0
    for src in range(2 * n):
        dist = [-1] * (2 * n)
        dist[src] = 0
        dq = deque([src])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w] = dist[v] + 1
                    dq.append(w)
        if min(dist) < 0:
            return False, "disconnected", None
        diam = max(diam, max(dist))
    if diam > 3:
        return False, f"diameter {diam} > 3", None
    return True, f"{2*n} vertices, {k}-regular, bipartite, diameter {diam}", hist


def covers(n, S):
    D = {(a - b) % n for a in S for b in S if a != b}
    return len(D) == n - 1


def bt_search(n, k):
    """Complete backtracking over S = {0} u T, T an increasing subset of {1..n-1} of size k-1.
    Prunes when over-cover > 2 (sound, see module docstring). Returns (number of solutions with 0 in S, first)."""
    cov = [0] * n
    S = [0]
    over = 0
    count = 0
    first = None

    def push(x):
        nonlocal over
        add = 0
        for a in S:
            for d in ((x - a) % n, (a - x) % n):
                if cov[d] >= 1:
                    add += 1
                cov[d] += 1
        S.append(x)
        over += add
        return add

    def pop(add):
        nonlocal over
        x = S.pop()
        for a in S:
            for d in ((x - a) % n, (a - x) % n):
                cov[d] -= 1
        over -= add

    def rec(start):
        nonlocal count, first
        if len(S) == k:
            if sum(1 for d in range(1, n) if cov[d]) == n - 1:
                count += 1
                if first is None:
                    first = list(S)
            return
        for x in range(start, n - (k - len(S)) + 1):
            add = push(x)
            if over <= 2:
                rec(x + 1)
            pop(add)

    rec(1)
    return count, first


def brute_count(n, k):
    """Naive enumeration of all k-subsets containing 0 (cross-check for small k only)."""
    from itertools import combinations
    cnt = 0
    for T in combinations(range(1, n), k - 1):
        if covers(n, (0,) + T):
            cnt += 1
    return cnt


def sat_search(n, k):
    """Complete SAT search. Returns ('SAT', S) | ('UNSAT', None)."""
    from pysat.card import CardEnc, EncType
    from pysat.solvers import Solver

    def x(g):
        return g + 1  # variables 1..n are x_0..x_{n-1}

    top = n
    cls = [[x(0)]]  # translation: 0 in S
    for d in range(1, (n - 1) // 2 + 1):
        ys = []
        for g in range(n):
            top += 1
            cls.append([-top, x(g)])
            cls.append([-top, x((g + d) % n)])
            ys.append(top)
        cls.append(ys)  # d = (g+d) - g in S - S for some g
    card = CardEnc.equals(lits=[x(g) for g in range(n)], bound=k, top_id=top, encoding=EncType.seqcounter)
    cls += card.clauses

    # No in-process time limit: CaDiCaL (pysat) does not support interrupt(), so the wall-clock limit is
    # enforced by the outer `timeout` command instead.
    with Solver(name="cadical153", bootstrap_with=cls) as s:
        if s.solve():
            model = s.get_model()
            S = sorted(l - 1 for l in model if 0 < l <= n)
            return "SAT", S
        return "UNSAT", None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ks", default="5,6,7,8,9,10,11,12,13,14,15,16")
    ap.add_argument("--bt-max-k", type=int, default=8, help="run the complete backtracking up to this k")
    args = ap.parse_args()

    print("k  n    group  bt(#S with 0, time)        sat(result, time)     verified", flush=True)
    for k in [int(t) for t in args.ks.split(",")]:
        n = k * k - k - 1
        f = factorize(n)
        assert n % 2 == 1 and all(e == 1 for e in f.values()), "non-squarefree n: more abelian groups"
        line = f"{k:<2} {n:<4} Z{n:<5}"
        bt_cnt = None
        if k <= args.bt_max_k:
            t0 = time.time()
            bt_cnt, bt_first = bt_search(n, k)
            line += f" {bt_cnt:>6} sols {time.time()-t0:7.2f}s  "
        else:
            line += " " * 26
        t0 = time.time()
        res, S = sat_search(n, k)
        line += f"  {res:<8} {time.time()-t0:8.2f}s  "
        if res == "SAT":
            if not covers(n, S):
                line += " SAT-model-does-not-cover (BUG)"
            ok, msg, hist = verify(n, k, S)
            line += f" {'OK' if ok else 'FAIL'} S={S} cn-hist={hist}"
            if bt_cnt == 0:
                line += "  !! bt says none but SAT found one (BUG)"
        elif res == "UNSAT" and bt_cnt is not None:
            line += " (bt agrees: none)" if bt_cnt == 0 else "  !! bt found solutions but SAT says UNSAT (BUG)"
        print(line, flush=True)


if __name__ == "__main__":
    main()
