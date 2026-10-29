#!/usr/bin/env python3
"""Squad conics-r2, card c6: automorphisms of the four-hat structure S over PG(2,q), q prime.

Frames: A=(0,1,0), ell=[0,1,0], X_a=(1,0,0), X_c=(0,0,1), X_0=(1,0,1), X_1=(1,0,t), t not in {0,1}.
The incidences are written from rules (R1)-(R6) of research/squads/conics-r1/BRIEF.md (independent code,
nothing imported from research/synthetic/conics/). Groups come from pynauty:
  collineations  = automorphisms of the incidence graph with points and lines coloured differently;
  correlations   = side-swapping automorphisms of the uncoloured incidence graph;
  polarities     = side-swapping involutions.
Full groups are enumerated by closure of the pynauty generators (cross-checked against pynauty's orders).
"""
import sys, itertools, json, hashlib
from collections import deque, Counter

import pynauty

A = (0, 1, 0)
ELL = (0, 1, 0)


def inv(a, q):
    return pow(a, q - 2, q)


def norm(v, q):
    v = tuple(x % q for x in v)
    for x in v:
        if x:
            i = inv(x, q)
            return tuple((y * i) % q for y in v)
    return None


def dot(u, v, q):
    return sum(a * b for a, b in zip(u, v)) % q


def cross(u, v, q):
    return ((u[1] * v[2] - u[2] * v[1]) % q,
            (u[2] * v[0] - u[0] * v[2]) % q,
            (u[0] * v[1] - u[1] * v[0]) % q)


def pg(q):
    return sorted({norm(v, q) for v in itertools.product(range(q), repeat=3) if any(v)})


def build(q, X, hats, T, rho, pi):
    """Incidence structure S. X: label -> normalized point on ell; hats: list of labels (contains 'a').
    rho, pi: dicts on T. Returns (V, E, NP) with E a set of (point_vertex, line_vertex) pairs.
    Vertices: points 0..NP-1 (PG points 0..N-1, Q = N, H_s = N+1+k); lines NP..V-1
    (PG line j is vertex NP+j, M = NP+N, K_s = NP+N+1+k)."""
    P = pg(q)
    N = len(P)
    pid = {p: i for i, p in enumerate(P)}
    NP = N + 1 + len(hats)
    V = 2 * NP
    Lv = lambda j: NP + j
    Qp = N
    Hp = {s: N + 1 + k for k, s in enumerate(hats)}
    Mln = NP + N
    Kln = {s: NP + N + 1 + k for k, s in enumerate(hats)}
    Xi = {s: pid[X[s]] for s in hats}
    lam = {s: pid[norm(cross(A, X[s], q), q)] for s in hats}   # PG line index of A X_s
    ell = pid[norm(ELL, q)]
    Aid = pid[norm(A, q)]
    ellpts = [i for i in range(N) if dot(P[i], ELL, q) == 0]
    for s in hats:
        assert dot(P[Xi[s]], ELL, q) == 0 and Xi[s] != Aid
    E = set()
    # R1: all PG incidences except (X_s, lam_s) for s in S, plus (X_t, lam_{rho(t)}) for t in T
    removed = {(Xi[s], Lv(lam[s])) for s in hats}
    for i in range(N):
        for j in range(N):
            if dot(P[i], P[j], q) == 0 and (i, Lv(j)) not in removed:
                E.add((i, Lv(j)))
    for t in T:
        E.add((Xi[t], Lv(lam[rho[t]])))
    # R2: H_s on every PG line through X_s other than ell
    for s in hats:
        for j in range(N):
            if j != ell and dot(P[Xi[s]], P[j], q) == 0:
                E.add((Hp[s], Lv(j)))
    # R3: K_s contains every PG point of lam_s other than A
    for s in hats:
        for i in range(N):
            if i != Aid and dot(P[i], P[lam[s]], q) == 0:
                E.add((i, Kln[s]))
    # R4: M contains the points of ell* (ell minus X_t, t in T) and every H_s
    Tpts = {Xi[t] for t in T}
    for i in ellpts:
        if i not in Tpts:
            E.add((i, Mln))
    for s in hats:
        E.add((Hp[s], Mln))
    # R5: Q on the lines of Lam* (lines through A other than lam_t, t in T) and on every K_s
    lamT = {lam[t] for t in T}
    for j in range(N):
        if dot(P[Aid], P[j], q) == 0 and j not in lamT:
            E.add((Qp, Lv(j)))
    for s in hats:
        E.add((Qp, Kln[s]))
    # R6: A on K_a; H_a on ell; H_t on K_{pi(t)}
    E.add((Aid, Kln['a']))
    E.add((Hp['a'], Lv(ell)))
    for t in T:
        E.add((Hp[t], Kln[pi[t]]))
    return V, E, NP


def adjacency(V, E):
    adj = {v: [] for v in range(V)}
    for (p, l) in E:
        adj[p].append(l)
        adj[l].append(p)
    return adj


def compose(g, h):          # (g o h)(x) = g(h(x))
    return tuple(g[x] for x in h)


def enumerate_group(gens, n, limit=3_000_000):
    idt = tuple(range(n))
    seen = {idt}
    dq = deque([idt])
    gens = [tuple(g) for g in gens]
    while dq:
        h = dq.popleft()
        for g in gens:
            k = compose(g, h)
            if k not in seen:
                seen.add(k)
                dq.append(k)
                if len(seen) > limit:
                    raise RuntimeError("group too large")
    return seen


def bfs_diam(V, adj):
    diam = 0
    for s in range(V):
        dist = {s: 0}
        dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    dq.append(y)
        if len(dist) != V:
            return None  # disconnected
        diam = max(diam, max(dist.values()))
    return diam


def analyse(q, X, hats, T, rho, pi, want_group=True):
    V, E, NP = build(q, X, hats, T, rho, pi)
    adj = adjacency(V, E)
    degs = Counter(len(adj[v]) for v in range(NP))
    degl = Counter(len(adj[v]) for v in range(NP, V))
    gcol = pynauty.Graph(V, directed=False, adjacency_dict=adj,
                         vertex_coloring=[set(range(NP)), set(range(NP, V))])
    gens_c, g1c, g2c, _, _ = pynauty.autgrp(gcol)
    Col_pn = round(g1c * 10 ** g2c)
    gunc = pynauty.Graph(V, directed=False, adjacency_dict=adj)
    gens_u, g1u, g2u, _, _ = pynauty.autgrp(gunc)
    Aut_pn = round(g1u * 10 ** g2u)
    cert = hashlib.sha256(pynauty.certificate(gunc)).hexdigest()[:16]
    out = dict(V=V, NP=NP, pts=len(range(NP)), deg_points=dict(degs), deg_lines=dict(degl),
               diam=bfs_diam(V, adj), Col_pynauty=Col_pn, Aut_pynauty=Aut_pn, cert=cert)
    if want_group:
        G = enumerate_group(gens_u, V)
        assert len(G) == Aut_pn, (len(G), Aut_pn)
        swap = [g for g in G if g[0] >= NP]
        for g in swap:
            assert all((g[v] >= NP) for v in range(NP)), "not side-consistent"
        keep = len(G) - len(swap)
        assert keep == Col_pn, (keep, Col_pn)
        idt = tuple(range(V))
        invols = [g for g in swap if compose(g, g) == idt]
        out.update(Col=keep, Aut=len(G), n_swap=len(swap), correlation=len(swap) > 0,
                   n_polarities=len(invols), polarity=len(invols) > 0)
        for g in invols:
            assert all(((g[l], g[p]) in E) for (p, l) in E), "involution not an automorphism"
            assert all(g[g[v]] == v for v in range(V))
        out['_invols'] = invols
        out['_verified_invols'] = len(invols)
        out['_G'] = G
    return out, E, adj


def explicit_iso(V, E1, E2):
    """Build an isomorphism of the uncoloured incidence graphs from pynauty canonical labellings and check it."""
    a1, a2 = adjacency(V, E1), adjacency(V, E2)
    lab1 = pynauty.canon_label(pynauty.Graph(V, directed=False, adjacency_dict=a1))
    lab2 = pynauty.canon_label(pynauty.Graph(V, directed=False, adjacency_dict=a2))
    pos1 = {v: i for i, v in enumerate(lab1)}
    f = [lab2[pos1[v]] for v in range(V)]
    ok = all(((f[p], f[l]) in E2) for (p, l) in E1) and len(E1) == len(E2)
    return ok


def theta_map(q, hats, tau, V, NP, N, P, pid, Hp, Kln, Qp, Mln):
    """theta of CLAIM 1 (conic polarity on PG, H_s <-> K_{tau s}, Q <-> M) as a vertex permutation."""
    th = [None] * V
    inv2 = inv(2, q)
    for i in range(N):
        x, y, z = P[i]
        pol = norm((z, -2 * y, x), q)            # polar line of point (x,y,z) under xz = y^2
        th[i] = NP + pid[pol]
    for j in range(N):
        a_, b_, c_ = P[j]
        pole = norm((c_, (-b_ * inv2) % q, a_), q)
        th[NP + j] = pid[pole]
    th[Qp] = Mln
    th[Mln] = Qp
    for s in hats:
        th[Hp[s]] = Kln[tau[s]]
        th[Kln[s]] = Hp[tau[s]]
    return th


def check_theta(q, X, hats, T, rho, pi, tau):
    V, E, NP = build(q, X, hats, T, rho, pi)
    N = len(pg(q))
    P = pg(q)
    pid = {p: i for i, p in enumerate(P)}
    Hp = {s: N + 1 + k for k, s in enumerate(hats)}
    Kln = {s: NP + N + 1 + k for k, s in enumerate(hats)}
    th = theta_map(q, hats, tau, V, NP, N, P, pid, Hp, Kln, N, NP + N)
    involution = all(th[th[v]] == v for v in range(V)) and sorted(th) == list(range(V))
    sidesw = all((th[v] >= NP) == (v < NP) for v in range(V))
    # flags (p, L) <-> (theta L, theta p)
    img = {(th[l], th[p]) for (p, l) in E}
    flagok = img == E
    return dict(involution=involution, swaps_sides=sidesw, flag_preserving=flagok)


def cr(p1, p2, p3, p4, q):
    d = lambda u, v: (u[0] * v[2] - u[2] * v[0]) % q     # det on (x, z) coordinates of points of ell
    den = d(p1, p4) * d(p2, p3) % q
    if den == 0:
        return None
    return d(p1, p3) * d(p2, p4) % q * inv(den, q) % q


def main():
    qs = [int(x) for x in sys.argv[1:]] or [5, 7]
    summary = {}
    for q in qs:
        print(f"===== q = {q} =====", flush=True)
        Z = (1, 0, 0)
        Zp = (0, 0, 1)
        hats4 = ['a', 'c', '0', '1']
        T4 = ['0', 'c', '1']
        rho4 = {'0': 'c', 'c': '1', '1': '0'}
        pi4 = rho4
        tau4 = {'a': 'a', 'c': 'c', '0': '1', '1': '0'}
        # sanity: three hats, conic frame (u=1), pi=(0 1), rho=identity
        X3 = {'a': Z, '0': (1, 0, 1), '1': norm((1, 0, -1), q)}
        out3, _, _ = analyse(q, X3, ['a', '0', '1'], ['0', '1'], {'0': '0', '1': '1'},
                             {'0': '1', '1': '0'}, want_group=False)
        th3 = check_theta(q, X3, ['a', '0', '1'], ['0', '1'], {'0': '0', '1': '1'}, {'0': '1', '1': '0'},
                          {'a': 'a', '0': '1', '1': '0'})
        print(f"sanity three hats (conic frame u=1): deg_pts={out3['deg_points']} deg_lines={out3['deg_lines']} "
              f"diam={out3['diam']} theta={th3}", flush=True)
        rows = {}
        Ts = [t for t in range(2, q)]           # t in GF(q) \ {0,1}
        pts_on_ell = None
        for t in Ts:
            X = {'a': Z, 'c': Zp, '0': (1, 0, 1), '1': (1, 0, t)}
            out, E, adj = analyse(q, X, hats4, T4, rho4, pi4)
            th = check_theta(q, X, hats4, T4, rho4, pi4, tau4)
            out['theta_conic_map'] = th
            out['CR_a_c_0_1'] = cr(X['a'], X['c'], X['0'], X['1'], q)
            print(f"t={t}: |Col|={out['Col']} |Aut|={out['Aut']} correlation={out['correlation']} "
                  f"polarities={out['n_polarities']} polarity={out['polarity']} "
                  f"CR={out['CR_a_c_0_1']} deg_pts={out['deg_points']} deg_lines={out['deg_lines']} "
                  f"diam={out['diam']} cert={out['cert']} theta_conic_map={th}", flush=True)
            rows[t] = {k: v for k, v in out.items() if not k.startswith('_')}
            rows[t]['verified_invols'] = out['_verified_invols']
        # isomorphism check: all ordered quadruples of distinct points on ell with CR = -1
        ellpts = [p for p in pg(q) if dot(p, ELL, q) == 0]
        nq = 0
        certs = Counter()
        for p1, p2, p3, p4 in itertools.permutations(ellpts, 4):
            if cr(p1, p2, p3, p4, q) != q - 1:
                continue
            nq += 1
            Xq = {'a': p1, 'c': p2, '0': p3, '1': p4}
            V, E, NP = build(q, Xq, hats4, T4, rho4, pi4)
            g = pynauty.Graph(V, directed=False, adjacency_dict=adjacency(V, E))
            certs[hashlib.sha256(pynauty.certificate(g)).hexdigest()[:16]] += 1
        print(f"harmonic quadruples (CR=-1) on ell: {nq}; distinct uncoloured incidence-graph certificates: "
              f"{len(certs)} {dict(certs)}", flush=True)
        # cross-t: are the frame graphs isomorphic to each other?
        cert_by_t = {t: rows[t]['cert'] for t in Ts}
        print("certificates by t:", cert_by_t, flush=True)
        Xh = {'a': Z, 'c': Zp, '0': (1, 0, 1), '1': (1, 0, q - 1)}
        Vh, Eh, _ = build(q, Xh, hats4, T4, rho4, pi4)
        for t in Ts:
            Xt = {'a': Z, 'c': Zp, '0': (1, 0, 1), '1': (1, 0, t)}
            _, Et, _ = build(q, Xt, hats4, T4, rho4, pi4)
            rows[t]['explicit_iso_to_t_minus1'] = explicit_iso(Vh, Eh, Et)
            print(f"t={t}: explicit isomorphism of incidence graphs to t=-1 frame: {rows[t]['explicit_iso_to_t_minus1']}",
                  flush=True)
        summary[q] = dict(
            rows={str(t): {k: rows[t][k] for k in ('Col', 'Aut', 'correlation', 'n_polarities', 'polarity',
                                                   'verified_invols', 'diam', 'cert', 'CR_a_c_0_1',
                                                   'explicit_iso_to_t_minus1')}
                  | {'theta_conic_map_ok': all(rows[t]['theta_conic_map'].values())} for t in Ts},
            harmonic_quadruples=nq, harmonic_distinct_certs=len(certs),
            sanity_three_hats_theta=th3)
    print(json.dumps(summary, indent=1, default=str))


if __name__ == '__main__':
    main()
