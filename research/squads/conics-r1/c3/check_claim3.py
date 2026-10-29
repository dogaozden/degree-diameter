#!/usr/bin/env python3
"""Card c3 (squad conics-r1): independent check of CLAIM 3 (explicit regular completion).

Own code. Only coords.GF (GF(q) arithmetic) is taken from research/plus2/coords.
Nothing is imported from research/synthetic/.

Per instance (q, kind in {three, four}, u):
  1. build S from the rules R1-R6 of BRIEF.md in the conic-adapted frame
     (X_a = Z, X_0 = (1,0,u), X_1 = (1,0,-u), and X_c = Z' for four hats);
  2. list the elements of degree q+1 and check they are old points/lines;
  3. build mu (polar(p) if p not on C, polar(p*) if p on C, p* = second point of C on Ap);
     check mu: deficient points -> deficient lines is a bijection and p not on mu(p);
  4. add the flags (p, mu(p)); check every element has degree exactly q+2;
  5. diameter of the incidence graph (BFS from every vertex);
  6. theta-self-polarity: flag (x, y) iff (theta(y), theta(x)) is a flag, for S and for the completion.
Writes results.json next to this file and prints one line per instance.
"""
import sys
import itertools
import json
import os
import collections

sys.path.insert(0, '/home/user/degree-diameter/research/plus2/coords')
import coords  # noqa: E402  (GF(q) arithmetic only)

HERE = os.path.dirname(os.path.abspath(__file__))


def field_ok(F):
    q = F.q
    for x in range(q):
        for y in range(q):
            if F.add(x, y) != F.add(y, x) or F.mul(x, y) != F.mul(y, x):
                return False
            for z in range(q):
                if F.mul(x, F.add(y, z)) != F.add(F.mul(x, y), F.mul(x, z)):
                    return False
                if F.mul(F.mul(x, y), z) != F.mul(x, F.mul(y, z)):
                    return False
    return True


def run(q, kind, u_name, F, u):
    add, mul, neg, inv = F.add, F.mul, F.neg, F.inv

    def sub(x, y):
        return add(x, neg(y))

    TWO = add(1, 1)
    INV2 = inv(TWO)
    rng = range(q)

    def norm(v):
        i = next(i for i in range(3) if v[i] != 0)
        s = inv(v[i])
        return tuple(mul(s, x) for x in v)

    def dot(p, L):
        s = 0
        for i in range(3):
            s = add(s, mul(p[i], L[i]))
        return s

    def cross(p, r):
        return (sub(mul(p[1], r[2]), mul(p[2], r[1])),
                sub(mul(p[2], r[0]), mul(p[0], r[2])),
                sub(mul(p[0], r[1]), mul(p[1], r[0])))

    def on_conic(p):                       # C: x z = y^2
        x, y, z = p
        return sub(mul(x, z), mul(y, y)) == 0

    def polar(p):                          # point (x,y,z) -> line [z,-2y,x]
        x, y, z = p
        return norm((z, neg(mul(TWO, y)), x))

    def pole(L):                           # line [a,b,c] -> point (c,-b/2,a)
        a, b, c = L
        return norm((c, mul(neg(b), INV2), a))

    pts = sorted({norm(v) for v in itertools.product(rng, repeat=3) if any(v)})
    lines = pts
    assert len(pts) == q * q + q + 1
    for p in pts:                          # polarity sanity
        assert (dot(p, polar(p)) == 0) == on_conic(p)
        assert pole(polar(p)) == p

    # ---- frame
    A = norm((0, 1, 0))
    ell = norm((0, 1, 0))
    assert polar(A) == ell
    Z, Zp = norm((1, 0, 0)), norm((0, 0, 1))
    assert on_conic(Z) and on_conic(Zp)
    X = {'a': Z, '0': norm((1, 0, u)), '1': norm((1, 0, neg(u)))}
    if kind == 'four':
        X['c'] = Zp
        S = ['0', '1', 'a', 'c']
        T = ['0', 'c', '1']
        rho = {'0': 'c', 'c': '1', '1': '0'}     # sigma
        pi = dict(rho)                            # pi = rho = sigma
    else:
        S = ['0', '1', 'a']
        T = ['0', '1']
        rho = {'0': '0', '1': '1'}                # identity
        pi = {'0': '1', '1': '0'}                 # (0 1)
    tau = {'0': '1', '1': '0', 'a': 'a', 'c': 'c'}
    lam = {s: norm(cross(A, X[s])) for s in S}    # lam_s = A X_s
    for s in S:
        assert dot(X[s], lam[s]) == 0 and dot(A, lam[s]) == 0
        assert dot(X[s], ell) == 0
    assert len({X[s] for s in S}) == len(S)

    def Pk(p):
        return ('P', p)

    def Lk(l):
        return ('L', l)

    # ---- S from R1-R6
    inc = set()
    removed = {(Pk(X[s]), Lk(lam[s])) for s in S}
    for p in pts:                                             # R1 (old part)
        for l in lines:
            if dot(p, l) == 0 and (Pk(p), Lk(l)) not in removed:
                inc.add((Pk(p), Lk(l)))
    for t in T:                                               # R1 (re-added flags)
        inc.add((Pk(X[t]), Lk(lam[rho[t]])))
    for s in S:                                               # R2: H_s on every line through X_s other than ell
        for l in lines:
            if dot(X[s], l) == 0 and l != ell:
                inc.add((('H', s), Lk(l)))
    for s in S:                                               # R3: K_s contains points of lam_s other than A
        for p in pts:
            if dot(p, lam[s]) == 0 and p != A:
                inc.add((Pk(p), ('K', s)))
    Tpts = {X[t] for t in T}
    for p in pts:                                             # R4: M contains ell* ...
        if dot(p, ell) == 0 and p not in Tpts:
            inc.add((Pk(p), ('M',)))
    for s in S:                                               # R4: ... and every H_s
        inc.add((('H', s), ('M',)))
    Tlines = {lam[t] for t in T}
    for l in lines:                                           # R5: Q on Lam*
        if dot(A, l) == 0 and l not in Tlines:
            inc.add((('Q',), Lk(l)))
    for s in S:                                               # R5: Q on every K_s
        inc.add((('Q',), ('K', s)))
    inc.add((Pk(A), ('K', 'a')))                              # R6: A on K_a
    inc.add((('H', 'a'), Lk(ell)))                            # R6: H_a on ell
    for t in T:                                               # R6: H_t on K_{pi(t)}
        inc.add((('H', t), ('K', pi[t])))

    def degrees(I):
        d = collections.Counter()
        for x, y in I:
            d[x] += 1
            d[y] += 1
        return d

    point_keys = [Pk(p) for p in pts] + [('Q',)] + [('H', s) for s in S]
    line_keys = [Lk(l) for l in lines] + [('M',)] + [('K', s) for s in S]
    nodes = point_keys + line_keys
    d0 = degrees(inc)
    assert all(d0[k] > 0 for k in nodes)
    base_max_ok = max(d0[k] for k in nodes) <= q + 2
    new_keys = [k for k in nodes if k[0] in ('Q', 'H', 'M', 'K')]
    new_base_all_q2 = all(d0[k] == q + 2 for k in new_keys)

    # ---- step 2: deficient elements (degree q+1)
    deficient_pts = [k for k in point_keys if d0[k] == q + 1]
    deficient_lns = [k for k in line_keys if d0[k] == q + 1]
    deficient_all_old = all(k[0] == 'P' for k in deficient_pts) and all(k[0] == 'L' for k in deficient_lns)

    # ---- step 3: mu
    def pstar(p):
        lp = norm(cross(A, p))                       # line A p
        assert dot(A, lp) == 0 and dot(p, lp) == 0
        others = [r for r in pts if dot(r, lp) == 0 and on_conic(r) and r != p]
        assert len(others) <= 1
        return others[0] if others else p            # tangent case: p* = p

    mu = {}
    tangent_cases = 0
    for k in deficient_pts:
        if k[0] != 'P':                       # a deficient new element: reported as failure below
            continue
        p = k[1]
        if on_conic(p):
            ps = pstar(p)
            if ps == p:
                tangent_cases += 1
            mu[k] = Lk(polar(ps))
        else:
            mu[k] = Lk(polar(p))
    img = [mu[k] for k in deficient_pts if k in mu]
    bijection = (len(set(img)) == len(img) == len(deficient_pts)
                 and set(img) == set(deficient_lns) and len(deficient_lns) == len(deficient_pts))
    p_not_on_mu = all(dot(k[1], m[1]) != 0 for k, m in mu.items())
    mu_targets_def = all(m in set(deficient_lns) for m in img)
    old_def = [k for k in deficient_pts if k[0] == 'P']
    n_def_on_C = sum(1 for k in old_def if on_conic(k[1]))
    n_def_on_ell = sum(1 for k in old_def if dot(k[1], ell) == 0)
    n_def_through_A = sum(1 for k in old_def if dot(k[1], A) == 0 and k[1] != A)

    # ---- step 4: completion
    inc2 = set(inc)
    for k in mu:
        e = (k, mu[k])
        assert e not in inc2
        inc2.add(e)
    d2 = degrees(inc2)
    deg_exact = all(d2[k] == q + 2 for k in nodes)
    max_deg2 = max(d2[k] for k in nodes)
    min_deg2 = min(d2[k] for k in nodes)

    # ---- step 5: diameter by BFS on the incidence graph
    def diameter(I):
        adj = collections.defaultdict(list)
        for x, y in I:
            adj[x].append(y)
            adj[y].append(x)
        diam, connected = 0, True
        for s0 in nodes:
            dist = {s0: 0}
            dq = collections.deque([s0])
            while dq:
                v = dq.popleft()
                for w in adj[v]:
                    if w not in dist:
                        dist[w] = dist[v] + 1
                        dq.append(w)
            if len(dist) != len(nodes):
                connected = False
            diam = max(diam, max(dist.values()))
        return diam, connected

    diam2, conn2 = diameter(inc2)
    diam_base, conn_base = diameter(inc)

    # ---- step 6: theta-self-polarity
    def theta(k):
        t = k[0]
        if t == 'P':
            return Lk(polar(k[1]))
        if t == 'L':
            return Pk(pole(k[1]))
        if t == 'H':
            return ('K', tau[k[1]])
        if t == 'K':
            return ('H', tau[k[1]])
        if t == 'Q':
            return ('M',)
        if t == 'M':
            return ('Q',)
        raise ValueError(k)

    theta_invol = all(theta(theta(k)) == k for k in nodes)

    def selfpolar(I):
        return {(theta(y), theta(x)) for (x, y) in I} == I

    selfpolar_base = selfpolar(inc)
    selfpolar_completed = selfpolar(inc2)
    # the completion flags themselves, as a set
    new_flags = {(k, mu[k]) for k in mu}
    new_flags_mapped = {(theta(y), theta(x)) for (x, y) in new_flags}

    passed = (base_max_ok and new_base_all_q2 and deficient_all_old and bijection and mu_targets_def
              and p_not_on_mu and deg_exact and diam2 == 3 and conn2 and theta_invol
              and selfpolar_base and selfpolar_completed and new_flags_mapped <= inc2)
    return {
        'q': q, 'kind': kind, 'u_name': u_name, 'u': u, 'u_is_square': any(mul(y, y) == u for y in rng),
        'n_points_S': len(point_keys), 'n_lines_S': len(line_keys),
        'base_max_deg_le_q+2': base_max_ok, 'new_elements_base_deg_q+2': new_base_all_q2,
        'n_deficient_points': len(deficient_pts), 'n_deficient_lines': len(deficient_lns),
        'deficient_all_old': deficient_all_old,
        'n_deficient_points_on_C': n_def_on_C,
        'n_deficient_points_on_ell': n_def_on_ell,
        'n_deficient_points_on_line_through_A': n_def_through_A,
        'tangent_cases_p_star_eq_p': tangent_cases,
        'mu_bijection_onto_deficient_lines': bijection, 'p_not_on_mu(p)': p_not_on_mu,
        'completed_all_deg_q+2': deg_exact, 'completed_deg_min_max': [min_deg2, max_deg2],
        'base_diameter': diam_base, 'base_connected': conn_base,
        'completed_diameter': diam2, 'completed_connected': conn2,
        'theta_involution': theta_invol, 'base_self_polar': selfpolar_base,
        'completed_self_polar': selfpolar_completed,
        'PASS': passed,
    }


def main():
    results = []
    for q in [3, 5, 7, 9, 11, 13]:
        F = coords.GF(q)
        assert field_ok(F), q
        squares = {F.mul(y, y) for y in range(1, q)}
        nonsq = min(x for x in range(1, q) if x not in squares)
        for kind in ['three', 'four']:
            if kind == 'four' and q < 3:
                continue
            for u_name, u in [('square', 1), ('nonsquare', nonsq)]:
                r = run(q, kind, u_name, F, u)
                results.append(r)
                print(f"q={q:<2} {kind:<5} u={u_name:<9}({u}) "
                      f"def_pts={r['n_deficient_points']:<4} def_lines={r['n_deficient_lines']:<4} "
                      f"def_on_C={r['n_deficient_points_on_C']:<3} tang={r['tangent_cases_p_star_eq_p']} "
                      f"bij={int(r['mu_bijection_onto_deficient_lines'])} p!in_mu={int(r['p_not_on_mu(p)'])} "
                      f"deg={r['completed_deg_min_max']} diam={r['completed_diameter']} "
                      f"selfpolar={int(r['base_self_polar'])}/{int(r['completed_self_polar'])} "
                      f"PASS={r['PASS']}")
    n_pass = sum(1 for r in results if r['PASS'])
    print(f"instances={len(results)} passing={n_pass} valid={n_pass == len(results)}")
    with open(os.path.join(HERE, 'results.json'), 'w') as f:
        json.dump({'instances': results, 'passing': n_pass, 'total': len(results)}, f, indent=1)


if __name__ == '__main__':
    main()
