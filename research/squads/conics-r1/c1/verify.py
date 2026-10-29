#!/usr/bin/env python3
"""c1 of squad conics-r1: independent check of CLAIM 1 and CLAIM 2 (BRIEF.md).

Written from the brief's definitions only; does not use research/synthetic/conics.
Prime fields, plain mod-p arithmetic. Prints one line per (q, kind, u) instance.
"""
import itertools
from collections import deque


def norm(v, q):
    """Normalize a nonzero triple mod q so its first nonzero entry is 1."""
    v = tuple(x % q for x in v)
    for x in v:
        if x:
            inv = pow(x, q - 2, q)
            return tuple((y * inv) % q for y in v)
    raise ValueError("zero vector")


def proj_points(q):
    s = set()
    for v in itertools.product(range(q), repeat=3):
        if any(v):
            s.add(norm(v, q))
    return sorted(s)


def dot(a, b, q):
    return (a[0] * b[0] + a[1] * b[1] + a[2] * b[2]) % q


def cross(a, b, q):
    return ((a[1] * b[2] - a[2] * b[1]) % q,
            (a[2] * b[0] - a[0] * b[2]) % q,
            (a[0] * b[1] - a[1] * b[0]) % q)


def polar_of_point(p, q):
    """Point (x,y,z) -> line [z, -2y, x]."""
    x, y, z = p
    return norm((z, -2 * y, x), q)


def pole_of_line(L, q):
    """Line [a,b,c] -> point (c, -b/2, a)."""
    a, b, c = L
    inv2 = pow(2, q - 2, q)
    return norm((c, -b * inv2, a), q)


def build(q, kind, u):
    A = (0, 1, 0)
    ell = (0, 1, 0)          # line [0,1,0], i.e. y = 0
    X = {'a': norm((1, 0, 0), q), '0': norm((1, 0, u), q), '1': norm((1, 0, -u), q)}
    if kind == 'three':
        S = ['0', '1', 'a']
        T = ['0', '1']
        pi = {'0': '1', '1': '0'}
        rho = {'0': '0', '1': '1'}          # identity for three hats
        tau = {'0': '1', '1': '0', 'a': 'a'}
    else:
        X['c'] = norm((0, 0, 1), q)
        S = ['0', '1', 'a', 'c']
        T = ['0', 'c', '1']
        sigma = {'0': 'c', 'c': '1', '1': '0'}
        pi = sigma
        rho = sigma
        tau = {'0': '1', '1': '0', 'a': 'a', 'c': 'c'}
    lam = {s: norm(cross(A, X[s], q), q) for s in S}   # line A X_s

    P0 = proj_points(q)      # old points
    L0 = P0                  # old lines (same triples)
    I = set()                # flags: (point label, line label)

    # R1: old incidences minus (X_s, lam_s) for s in S, plus (X_t, lam_rho(t)) for t in T
    deleted = {(X[s], lam[s]) for s in S}
    for p in P0:
        for l in L0:
            if dot(p, l, q) == 0 and (p, l) not in deleted:
                I.add((('P', p), ('L', l)))
    for t in T:
        I.add((('P', X[t]), ('L', lam[rho[t]])))

    # R2: H_s on every old line through X_s other than ell
    for s in S:
        for l in L0:
            if l != ell and dot(X[s], l, q) == 0:
                I.add((('H', s), ('L', l)))

    # R3: K_s contains every point of lam_s other than A
    for s in S:
        for p in P0:
            if p != A and dot(p, lam[s], q) == 0:
                I.add((('P', p), ('K', s)))

    # R4: M contains ell* (points of ell other than X_t, t in T) and every H_s
    Xt = {X[t] for t in T}
    for p in P0:
        if dot(p, ell, q) == 0 and p not in Xt:
            I.add((('P', p), ('M',)))
    for s in S:
        I.add((('H', s), ('M',)))

    # R5: Q on the lines of Lam* (lines through A other than lam_t, t in T) and on every K_s
    lamT = {lam[t] for t in T}
    for l in L0:
        if dot(A, l, q) == 0 and l not in lamT:
            I.add((('Q',), ('L', l)))
    for s in S:
        I.add((('Q',), ('K', s)))

    # R6: A on K_a; H_a on ell; H_t on K_pi(t) for t in T
    I.add((('P', A), ('K', 'a')))
    I.add((('H', 'a'), ('L', ell)))
    for t in T:
        I.add((('H', t), ('K', pi[t])))

    points = [('P', p) for p in P0] + [('Q',)] + [('H', s) for s in S]
    lines = [('L', l) for l in L0] + [('M',)] + [('K', s) for s in S]

    def theta(x):
        k = x[0]
        if k == 'P':
            return ('L', polar_of_point(x[1], q))
        if k == 'L':
            return ('P', pole_of_line(x[1], q))
        if k == 'H':
            return ('K', tau[x[1]])
        if k == 'K':
            return ('H', tau[x[1]])
        if k == 'Q':
            return ('M',)
        if k == 'M':
            return ('Q',)
        raise ValueError(x)

    return dict(q=q, kind=kind, u=u, S=S, I=I, points=points, lines=lines, theta=theta)


def bfs_all(adj, nodes):
    """Return (connected, diameter) of graph adj over nodes."""
    diam = 0
    connected = True
    n = len(nodes)
    for src in nodes:
        dist = {src: 0}
        dq = deque([src])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1
                    dq.append(y)
        if len(dist) < n:
            connected = False
        else:
            diam = max(diam, max(dist.values()))
    return connected, diam


def check(inst):
    q = inst['q']
    I = inst['I']
    points = inst['points']
    lines = inst['lines']
    theta = inst['theta']
    pset, lset = set(points), set(lines)

    # sanity: every flag refers to elements of S
    flags_ok = all(p in pset and L in lset for (p, L) in I)

    # CLAIM 1a: theta is an involution exchanging points and lines
    th_ok = (all(theta(x) in lset for x in points) and
             all(theta(x) in pset for x in lines) and
             all(theta(theta(x)) == x for x in points + lines))

    # CLAIM 1b: p I L <=> theta(L) I theta(p)
    flag_ok = all(((p, L) in I) == ((theta(L), theta(p)) in I)
                  for p in points for L in lines)

    # CLAIM 1c: max degree of S is q+2 (over points and lines)
    pdeg = {p: 0 for p in points}
    ldeg = {L: 0 for L in lines}
    plines = {p: set() for p in points}
    lpts = {L: set() for L in lines}
    for (p, L) in I:
        pdeg[p] += 1
        ldeg[L] += 1
        plines[p].add(L)
        lpts[L].add(p)
    maxdeg = max(max(pdeg.values()), max(ldeg.values()))
    deg_ok = (maxdeg == q + 2)

    # CLAIM 1d: diameter 3 of incidence graph (points share a line, lines share a point)
    pp_ok = all(plines[p] & plines[r] for p in points for r in points if p != r)
    ll_ok = all(lpts[L] & lpts[M] for L in lines for M in lines if L != M)
    adj = {x: [] for x in points + lines}
    for (p, L) in I:
        adj[p].append(L)
        adj[L].append(p)
    inc_conn, inc_diam = bfs_all(adj, points + lines)
    inc_ok = pp_ok and ll_ok and inc_conn and inc_diam == 3

    # CLAIM 2: folded graph G on points of S, p ~ r iff p != r and p I theta(r)
    G = {p: set() for p in points}
    for p in points:
        for r in points:
            if p != r and (p, theta(r)) in I:
                G[p].add(r)
    g_sym = all((r in G[p]) == (p in G[r]) for p in points for r in points)
    gmax = max(len(G[p]) for p in points)
    g_conn, g_diam = bfs_all(G, points)
    nV = len(points)
    nV_expected = q * q + q + (5 if inst['kind'] == 'three' else 6)
    g_ok = (g_sym and gmax <= q + 2 and g_conn and g_diam == 2 and nV == nV_expected)

    ok = flags_ok and th_ok and flag_ok and deg_ok and inc_ok and g_ok
    return dict(ok=ok, flags_ok=flags_ok, th_ok=th_ok, flag_ok=flag_ok, maxdeg=maxdeg,
                deg_ok=deg_ok, pp_ok=pp_ok, ll_ok=ll_ok, inc_diam=inc_diam,
                g_sym=g_sym, gmax=gmax, g_conn=g_conn, g_diam=g_diam, nV=nV)


def main():
    cases = []
    for q in [3, 5, 7, 11, 13]:
        us = [u for u in range(1, q) if (2 * u) % q != 0]   # u != -u (all of GF(q)* for odd q)
        cases.append((q, 'three', us))
        cases.append((q, 'four', [1] if q == 3 else us))   # q=3: ell has 4 points, use u=1
    total = 0
    passed = 0
    for q, kind, us in cases:
        for u in us:
            total += 1
            inst = build(q, kind, u)
            r = check(inst)
            passed += int(r['ok'])
            print(f"q={q:2d} kind={kind:5s} u={u:2d} | theta_involution={r['th_ok']} "
                  f"flags_pol={r['flag_ok']} flags_in_S={r['flags_ok']} maxdeg_S={r['maxdeg']} "
                  f"(q+2={q + 2}) inc_pts_share_line={r['pp_ok']} inc_lines_share_pt={r['ll_ok']} "
                  f"inc_diam={r['inc_diam']} | G_sym={r['g_sym']} maxdeg_G={r['gmax']} "
                  f"G_diam={r['g_diam']} G_conn={r['g_conn']} nV={r['nV']} "
                  f"=> {'PASS' if r['ok'] else 'FAIL'}")
    print(f"SUMMARY passed={passed} total={total} valid={passed == total}")


if __name__ == '__main__':
    main()
