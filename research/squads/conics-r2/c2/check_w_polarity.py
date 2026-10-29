#!/usr/bin/env python3
"""Card c2 of squad conics-r2: check Proposition 2.2 of research/synthetic/CONICS.md
(the polarity picture W(2^{2e+1})[j*O, j*S]) at q = 2, and at q = 8 if a polarity is found.

Usage (THREADS=1):
    OMP_NUM_THREADS=1 timeout 900 nice -n 10 <venv>/bin/python check_w_polarity.py 2
    OMP_NUM_THREADS=1 timeout 900 nice -n 10 <venv>/bin/python check_w_polarity.py 8 SECONDS

Self-contained: GF(2^k) tables are built here (no import from research/synthetic/conics/).
Writes result_q<q>.json next to this file.
"""
import itertools
import json
import os
import random
import sys
import time
from collections import deque

import numpy as np
import pynauty

HERE = os.path.dirname(os.path.abspath(__file__))
POLY = {1: 0b11, 3: 0b1011}  # x+1 (GF(2)) and x^3+x+1 (GF(8)), irreducible


def gf2k(k):
    """Multiplication and inverse tables of GF(2^k); addition is XOR."""
    poly, q = POLY[k], 1 << k

    def mul(a, b):
        r = 0
        for i in range(k):
            if (b >> i) & 1:
                r ^= a << i
        for i in range(2 * k - 2, k - 1, -1):
            if (r >> i) & 1:
                r ^= poly << (i - k)
        return r

    M = [[mul(a, b) for b in range(q)] for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if M[a][b] == 1)  # raises if not a field
    return q, M, inv


def build_W(q, M, inv):
    """Points and totally isotropic lines of W(q) in PG(3,q), form x0y1-x1y0+x2y3-x3y2."""
    def B(x, y):
        return M[x[0]][y[1]] ^ M[x[1]][y[0]] ^ M[x[2]][y[3]] ^ M[x[3]][y[2]]

    def norm(v):
        c = next(c for c in v if c)
        ic = inv[c]
        return tuple(M[ic][x] for x in v)

    pts = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)})
    pid = {p: i for i, p in enumerate(pts)}
    lines = set()
    for a, b in itertools.combinations(range(len(pts)), 2):
        p, r = pts[a], pts[b]
        if B(p, r):
            continue
        span = {pid[norm(tuple(M[s][p[i]] ^ M[t][r[i]] for i in range(4)))]
                for s in range(q) for t in range(q) if s or t}
        assert len(span) == q + 1
        lines.add(tuple(sorted(span)))
    lines = sorted(lines)
    Inc = np.zeros((len(pts), len(lines)), dtype=bool)
    for L, on in enumerate(lines):
        Inc[list(on), L] = True
    return pts, Inc


def check_gq(Inc, s, t):
    """GQ(s,t) axioms: sizes, two points on <= 1 line, unique projection, no triangles."""
    I = Inc.astype(np.int64)
    n, m = Inc.shape
    out = {"points": n, "lines": m, "expected_points": (s + 1) * (s * t + 1),
           "expected_lines": (t + 1) * (s * t + 1),
           "pts_per_line": sorted(set(I.sum(axis=0).tolist())),
           "lines_per_pt": sorted(set(I.sum(axis=1).tolist()))}
    G = I @ I.T
    np.fill_diagonal(G, 0)
    out["two_points_on_at_most_one_line"] = bool(G.max() <= 1)
    A = (G > 0).astype(np.int64)
    Q = A @ I  # Q[p, L] = points of L collinear with p
    out["gq3_unique_projection"] = bool((Q[I == 0] == 1).all())
    out["incident_projection_is_s"] = bool((Q[I == 1] == s).all())
    tri = int(np.trace(A @ A @ A)) // 6
    out["triangles"] = tri
    out["triangles_expected"] = m * (s + 1) * s * (s - 1) // 6
    out["pass"] = bool(
        n == out["expected_points"] and m == out["expected_lines"]
        and out["pts_per_line"] == [s + 1] and out["lines_per_pt"] == [t + 1]
        and out["two_points_on_at_most_one_line"] and out["gq3_unique_projection"]
        and out["incident_projection_is_s"] and tri == out["triangles_expected"])
    return out


def incidence_graph(Inc):
    n, m = Inc.shape
    adj = {x: [int(n + L) for L in np.flatnonzero(Inc[x])] for x in range(n)}
    for L in range(m):
        adj[n + L] = [int(x) for x in np.flatnonzero(Inc[:, L])]
    return pynauty.Graph(n + m, directed=False, adjacency_dict=adj)


def graph_diameter(adj):
    """All-pairs BFS; None if disconnected."""
    N, D = len(adj), 0
    for s in range(N):
        dist = [-1] * N
        dist[s] = 0
        dq = deque([s])
        while dq:
            u = dq.popleft()
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = dist[u] + 1
                    dq.append(v)
        if min(dist) < 0:
            return None
        D = max(D, max(dist))
    return D


def polarity_core(Inc, Tp, Tl):
    """Tp[x] = line theta(x) for points; Tl[L] = point theta(L) for lines."""
    n, m = Inc.shape
    out = {}
    out["bijection"] = bool(n == m and sorted(Tp.tolist()) == list(range(m))
                            and sorted(Tl.tolist()) == list(range(n)))
    out["involution"] = bool((Tl[Tp] == np.arange(n)).all() and (Tp[Tl] == np.arange(m)).all())
    # p I L  <=>  theta(L) I theta(p)   (point theta(L), line theta(p))
    out["p_I_L_iff_thetaL_I_thetap"] = bool((Inc.T == Inc[np.ix_(Tl, Tp)]).all())
    out["pass"] = all(out[k] for k in ("bijection", "involution", "p_I_L_iff_thetaL_I_thetap"))
    return out


def polarity_ovoid_spread(Inc, Tp, Tl, q):
    n, m = Inc.shape
    abs_pts = np.flatnonzero(Inc[np.arange(n), Tp])   # p I theta(p)
    abs_lines = np.flatnonzero(Inc[Tl, np.arange(m)])  # theta(L) I L
    out = {"n_absolute_points": int(len(abs_pts)), "n_absolute_lines": int(len(abs_lines))}
    out["absolute_points_ovoid"] = bool(len(abs_pts) == q * q + 1
                                        and (Inc[abs_pts].sum(axis=0) == 1).all())
    out["absolute_lines_spread"] = bool(len(abs_lines) == q * q + 1
                                        and (Inc[:, abs_lines].sum(axis=1) == 1).all())
    out["absolute_lines_are_theta_of_absolute_points"] = bool(
        set(Tp[abs_pts].tolist()) == set(abs_lines.tolist()))
    out["pass"] = all(out[k] for k in ("absolute_points_ovoid", "absolute_lines_spread",
                                       "absolute_lines_are_theta_of_absolute_points"))
    return out, abs_pts, abs_lines


def build_structure(Inc, Tp, Tl, abs_pts, abs_lines, j):
    """W(q)[j*O, j*S]: clones of O-points (on the lines through them), j shadow lines over each
    S-line (containing exactly its points). i-th clone of p <-> i-th shadow over theta(p)."""
    n, m = Inc.shape
    O = [int(p) for p in abs_pts]
    S = [int(M) for M in abs_lines]
    posO = {p: k for k, p in enumerate(O)}
    posS = {M: k for k, M in enumerate(S)}
    assert {int(Tp[p]) for p in O} == set(S) and {int(Tl[M]) for M in S} == set(O)
    Np, Nl = n + len(O) * j, m + len(S) * j
    I = np.zeros((Np, Nl), dtype=bool)
    I[:n, :m] = Inc
    Tp2 = np.full(Np, -1, dtype=np.int64)
    Tl2 = np.full(Nl, -1, dtype=np.int64)
    Tp2[:n] = Tp
    Tl2[:m] = Tl
    for p in O:
        for i in range(j):
            c = n + posO[p] * j + i
            I[c, :m] = Inc[p]
            Tp2[c] = m + posS[int(Tp[p])] * j + i
    for M in S:
        for i in range(j):
            sh = m + posS[M] * j + i
            I[:n, sh] = Inc[:, M]
            Tl2[sh] = n + posO[int(Tl[M])] * j + i
    return I, Tp2, Tl2


def structure_checks(I, Tp2, Tl2, q, j):
    Np, Nl = I.shape
    out = {"j": j, "points": Np, "lines": Nl,
           "expected_vertices": (q + 1 + j) * (q * q + 1)}
    out["polarity"] = polarity_core(I, Tp2, Tl2) if Np == Nl else {"pass": False}
    out["max_degree_incidence"] = int(max(I.sum(axis=1).max(), I.sum(axis=0).max()))
    adj = [(np.flatnonzero(I[p]) + Np).tolist() for p in range(Np)]
    adj += [np.flatnonzero(I[:, L]).tolist() for L in range(Nl)]
    out["incidence_diameter"] = graph_diameter(adj)
    Af = I[:, Tp2].copy()  # Af[p, r] = p I theta(r)  (polarity graph)
    np.fill_diagonal(Af, False)
    out["folded_vertices"] = Np
    out["folded_symmetric"] = bool((Af == Af.T).all())
    out["folded_max_degree"] = int(Af.sum(axis=1).max())
    out["folded_diameter"] = graph_diameter([np.flatnonzero(Af[p]).tolist() for p in range(Np)])
    out["pass"] = bool(
        out["polarity"]["pass"] and Np == Nl == out["expected_vertices"]
        and out["max_degree_incidence"] == q + 1 + j
        and out["incidence_diameter"] == 4
        and out["folded_symmetric"]
        and out["folded_max_degree"] <= q + 1 + j
        and out["folded_diameter"] is not None and out["folded_diameter"] <= 3)
    return out


def closure(gens, N):
    ident = tuple(range(N))
    seen, frontier = {ident}, [ident]
    while frontier:
        nxt = []
        for g in frontier:
            for h in gens:
                gh = tuple(g[h[i]] for i in range(N))
                if gh not in seen:
                    seen.add(gh)
                    nxt.append(gh)
        frontier = nxt
    return seen


def random_involutions(gens, n, seconds, want, seed):
    """Product replacement on the nauty generators; keep side-swapping involutions."""
    N2 = 2 * n
    rng = random.Random(seed)
    ar = np.arange(N2, dtype=np.int64)
    slots = [np.array(gens[i % len(gens)], dtype=np.int64) for i in range(10)]

    def inverse(p):
        r = np.empty_like(p)
        r[p] = ar
        return r

    def step():
        i, j = rng.sample(range(10), 2)
        if rng.random() < 0.5:
            slots[i] = slots[i][slots[j]]
        else:
            slots[i] = slots[i][inverse(slots[j])]

    for _ in range(500):
        step()
    found, trials, t0 = [], 0, time.time()
    while len(found) < want and time.time() - t0 < seconds:
        for _ in range(2000):
            step()
            trials += 1
            g = slots[rng.randrange(10)]
            if g[0] >= n and (g[g] == ar).all() and (g[:n] >= n).all():
                found.append(g.copy())
                if len(found) >= want:
                    break
    return found, trials, time.time() - t0


def main():
    q = int(sys.argv[1])
    k = {2: 1, 8: 3}[q]
    seconds = float(sys.argv[2]) if len(sys.argv) > 2 else 300.0
    t0 = time.time()
    _, M, inv = gf2k(k)
    pts, Inc = build_W(q, M, inv)
    n, m = Inc.shape
    res = {"q": q, "points": n, "lines": m}
    res["gq"] = check_gq(Inc, q, q)

    G = incidence_graph(Inc)
    gens, g1, g2, _, _ = pynauty.autgrp(G)
    res["nauty_group_order"] = float(g1) * 10.0 ** g2
    A2 = np.zeros((2 * n, 2 * n), dtype=bool)
    A2[:n, n:] = Inc
    A2[n:, :n] = Inc.T
    res["nauty_gens_are_automorphisms"] = bool(
        all((A2[np.ix_(np.array(g), np.array(g))] == A2).all() for g in gens))
    res["nauty_seconds"] = round(time.time() - t0, 2)

    if q == 2:
        allg = closure(gens, 2 * n)
        res["closure_group_size"] = len(allg)
        cands = [g for g in allg
                 if all(g[x] >= n for x in range(n))
                 and all(g[g[i]] == i for i in range(2 * n))]
        res["search"] = "full group closure"
    else:
        cands, trials, secs = random_involutions(gens, n, seconds, want=3, seed=1)
        res["search"] = {"method": "product replacement", "trials": trials,
                         "seconds": round(secs, 1), "found": len(cands)}

    res["n_polarities_found"] = len(cands)
    entries = []
    for g in cands:
        g = np.asarray(g, dtype=np.int64)
        Tp, Tl = g[:n] - n, g[n:]
        core = polarity_core(Inc, Tp, Tl)
        ov, abs_pts, abs_lines = polarity_ovoid_spread(Inc, Tp, Tl, q)
        e = {"polarity_core": core, "absolute": ov, "structures": []}
        if core["pass"] and ov["pass"]:
            for j in (0, 1, 2):
                I, Tp2, Tl2 = build_structure(Inc, Tp, Tl, abs_pts, abs_lines, j)
                e["structures"].append(structure_checks(I, Tp2, Tl2, q, j))
        e["pass"] = bool(core["pass"] and ov["pass"]
                         and all(s["pass"] for s in e["structures"]) and len(e["structures"]) == 3)
        entries.append(e)
    res["polarities"] = entries
    res["gq_pass"] = res["gq"]["pass"]
    res["all_polarities_pass"] = bool(entries) and all(e["pass"] for e in entries)
    # score: (q, j) pairs with j in {1,2} fully verified on the first polarity found
    first = entries[0] if entries else None
    res["verified_jq_pairs"] = [s["j"] for s in first["structures"] if s["pass"] and s["j"] >= 1] \
        if first else []
    res["total_seconds"] = round(time.time() - t0, 1)

    out_path = os.path.join(HERE, f"result_q{q}.json")
    with open(out_path, "w") as fh:
        json.dump(res, fh, indent=1, default=lambda o: o.tolist() if hasattr(o, "tolist") else str(o))
    summary = {k: res[k] for k in ("q", "points", "lines", "nauty_group_order", "n_polarities_found",
                                   "gq_pass", "all_polarities_pass", "verified_jq_pairs",
                                   "total_seconds")}
    summary["gq_pass_detail"] = {x: res["gq"][x] for x in ("pass", "triangles", "triangles_expected")}
    summary["first_polarity_absolute"] = first["absolute"] if first else None
    if first:
        summary["first_polarity_structures"] = [
            {x: s[x] for x in ("j", "points", "max_degree_incidence", "incidence_diameter",
                               "folded_vertices", "folded_max_degree", "folded_diameter", "pass")}
            for s in first["structures"]]
    print(json.dumps(summary, indent=1, default=lambda o: o.tolist() if hasattr(o, "tolist") else str(o)))
    print("wrote", out_path)


if __name__ == "__main__":
    main()
