#!/usr/bin/env python3
"""Card c5, squad conics-r1: independent check of the PG(3,q) elliptic-quadric claim.

Setting (q odd prime): points (X0:X1:X2:X3) of PG(3,q),
  beta(u,v) = u0 v1 - u1 v0 + u2 v3 - u3 v2,  x = (1:0:0:0),  x^perp = {X1 = 0}.
  E1: 2 X0 X1 = X2^2 - eps X3^2,   E2: 2 eps X0 X1 = X2^2 - eps X3^2,  eps a non-square.
For every z != x in {X1 = 0}: pi_z = z^perp, C_i = E_i cap pi_z.
  (a) C_i is a nondegenerate conic with q+1 points through x;
  (b) the line xz meets each E_i only in x;
  (c) every line of pi_z through z other than xz meets C1 u C2 in 2 points
      (counted with multiplicity: a point on both conics counts twice);
  (d) each such line is (2,0), (0,2) or (1,1) in terms of (|L cap C1|, |L cap C2|).
Original statement: every t.i. line of PG(3,q) not through x, minus its unique point z in
{X1 = 0}, meets E1 u E2 (multiplicity = number of E_i containing the point) in exactly 2.

Written from the task statement only. Does not use research/synthetic/conics/.
Usage: python3 check_pg3.py     (main run on q = 3,5,7,11,13; extra eps and a negative control)
"""
import itertools
import json
import time

ALLOWED = {(2, 0), (0, 2), (1, 1)}


def norm(v, q):
    """Normalize a nonzero vector so that its first nonzero coordinate is 1."""
    for c in v:
        if c % q:
            inv = pow(c % q, q - 2, q)
            return tuple((w * inv) % q for w in v)
    raise ValueError("zero vector")


def all_points(q):
    pts = set()
    for v in itertools.product(range(q), repeat=4):
        if any(v):
            pts.add(norm(v, q))
    return sorted(pts)


def beta(u, v, q):
    return (u[0] * v[1] - u[1] * v[0] + u[2] * v[3] - u[3] * v[2]) % q


def quad(p, q, eps, which):
    """Value of the quadratic form of E_which (0 on the quadric)."""
    x0, x1, x2, x3 = p
    if which == 1:
        val = 2 * x0 * x1 - x2 * x2 + eps * x3 * x3
    else:
        val = 2 * eps * x0 * x1 - x2 * x2 + eps * x3 * x3
    return val % q


def line_points(u, w, q):
    """The q+1 projective points of the line spanned by independent vectors u, w."""
    s = {norm(w, q)}
    for a in range(q):
        s.add(norm(tuple((u[k] + a * w[k]) % q for k in range(4)), q))
    return frozenset(s)


def all_lines(q):
    """One reduced-row-echelon basis (u, w) per 2-dimensional subspace of GF(q)^4."""
    for a in range(4):
        for b in range(a + 1, 4):
            free1 = [k for k in range(a + 1, 4) if k != b]
            free2 = [k for k in range(b + 1, 4)]
            for vals1 in itertools.product(range(q), repeat=len(free1)):
                u = [0] * 4
                u[a] = 1
                for k, v in zip(free1, vals1):
                    u[k] = v
                for vals2 in itertools.product(range(q), repeat=len(free2)):
                    w = [0] * 4
                    w[b] = 1
                    for k, v in zip(free2, vals2):
                        w[k] = v
                    yield tuple(u), tuple(w)


def rank_mod(rows, q):
    m = [[c % q for c in r] for r in rows]
    ncols = len(m[0])
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(m)) if m[i][c]), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = pow(m[r][c], q - 2, q)
        m[r] = [(w * inv) % q for w in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c]:
                f = m[i][c]
                m[i] = [(m[i][k] - f * m[r][k]) % q for k in range(ncols)]
        r += 1
    return r


def det3(G, q):
    (a, b, c), (d, e, f), (g, h, i) = G
    return (a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)) % q


def nonsquares(q):
    sq = {(a * a) % q for a in range(1, q)}
    return [e for e in range(1, q) if e not in sq]


def run(q, eps, x=(1, 0, 0, 0)):
    pts = all_points(q)
    assert len(pts) == q ** 3 + q ** 2 + q + 1
    plane = [p for p in pts if p[1] == 0]
    assert len(plane) == q * q + q + 1
    zs = [p for p in plane if p != x]
    onE = {1: set(), 2: set()}
    for p in pts:
        for i in (1, 2):
            if quad(p, q, eps, i) == 0:
                onE[i].add(p)
    quadric_sizes = (len(onE[1]), len(onE[2]))

    # ---- global enumeration of all t.i. lines not through x (original statement) ----
    by_z = {z: [] for z in zs}
    global_bad = []  # (z or None, reason)
    n_ti = 0
    n_ti_notx = 0
    for u, w in all_lines(q):
        if beta(u, w, q):
            continue
        n_ti += 1
        pl = line_points(u, w, q)
        if x in pl:
            continue
        n_ti_notx += 1
        zz = [p for p in pl if p[1] == 0]
        if len(zz) != 1:
            global_bad.append((None, "no unique point in X1=0"))
            continue
        z = zz[0]
        rest = pl - {z}
        n1 = sum(1 for p in rest if p in onE[1])
        n2 = sum(1 for p in rest if p in onE[2])
        by_z[z].append((pl, n1, n2))
        if not (n1 + n2 == 2 and (n1, n2) in ALLOWED):
            global_bad.append((z, "count %d+%d" % (n1, n2)))
    expect_ti = (q + 1) * (q * q + 1)
    expect_ti_notx = (q + 1) * q * q
    counts_ok = (n_ti == expect_ti and n_ti_notx == expect_ti_notx)

    # ---- per-z checks (claim (a)-(d)) ----
    z_results = []
    for z in zs:
        fails = []
        PI = [p for p in pts if beta(z, p, q) == 0]  # pi_z = z^perp
        if len(PI) != q * q + q + 1:
            fails.append("pi_size")
        if x not in PI:
            fails.append("x_not_in_pi")
        # (a) conics: q+1 points through x, nondegenerate
        C = {i: [p for p in PI if p in onE[i]] for i in (1, 2)}
        b3 = next(p for p in PI if rank_mod([x, z, p], q) == 3)
        basis = [x, z, b3]
        for i in (1, 2):
            if len(C[i]) != q + 1:
                fails.append("a_size%d=%d" % (i, len(C[i])))
            if x not in C[i]:
                fails.append("a_x%d" % i)
            G = [[0] * 3 for _ in range(3)]
            for r in range(3):
                for c in range(3):
                    s = tuple((basis[r][k] + basis[c][k]) % q for k in range(4))
                    G[r][c] = (quad(s, q, eps, i) - quad(basis[r], q, eps, i)
                               - quad(basis[c], q, eps, i)) % q
            if det3(G, q) == 0:
                fails.append("a_degenerate%d" % i)
        # (b) line xz meets each E_i only in x
        xz = line_points(x, z, q)
        for i in (1, 2):
            if {p for p in xz if p in onE[i]} != {x}:
                fails.append("b%d" % i)
        # (c),(d) the q lines of pi_z through z other than xz
        lines_z = {line_points(z, P, q) for P in PI if P != z}
        if len(lines_z) != q + 1:
            fails.append("lines_z_count=%d" % len(lines_z))
        if xz not in lines_z:
            fails.append("xz_missing")
        others = [L for L in lines_z if L != xz]
        if any(x in L for L in others):
            fails.append("x_on_other_line")
        for L in others:
            if not all(beta(z, p, q) == 0 for p in L):
                fails.append("line_not_in_pi")
            rest = L - {z}
            n1 = sum(1 for p in rest if p in onE[1])
            n2 = sum(1 for p in rest if p in onE[2])
            if not (n1 + n2 == 2 and (n1, n2) in ALLOWED):
                fails.append("cd%d_%d" % (n1, n2))
        # cross-check with the global enumeration: same lines, each good
        glob = by_z[z]
        if {pl for (pl, _, _) in glob} != set(others):
            fails.append("global_line_mismatch")
        if len(glob) != q:
            fails.append("global_count=%d" % len(glob))
        z_results.append((z, fails))

    global_bad_z = {}
    for zz_, reason in global_bad:
        global_bad_z.setdefault(zz_, []).append(reason)
    passing = 0
    fail_list = []
    for z, fails in z_results:
        allf = fails + global_bad_z.get(z, [])
        if not allf:
            passing += 1
        else:
            fail_list.append((z, allf))
    if None in global_bad_z:
        fail_list.append((None, global_bad_z[None]))
    valid = (passing == len(zs)) and counts_ok and not global_bad and not any(
        k is None for k in global_bad_z)
    return {
        "q": q, "eps": eps, "quadric_sizes": quadric_sizes,
        "n_ti": n_ti, "n_ti_expected": expect_ti,
        "n_ti_notx": n_ti_notx, "n_ti_notx_expected": expect_ti_notx,
        "z_total": len(zs), "z_pass": passing, "global_bad": len(global_bad),
        "fail_sample": fail_list[:5], "valid": valid,
    }


def main():
    t0 = time.time()
    main_rows = []
    print("== main run: smallest non-square eps, all z != x in X1=0 ==")
    for q in [3, 5, 7, 11, 13]:
        eps = nonsquares(q)[0]
        r = run(q, eps)
        main_rows.append(r)
        print(json.dumps(r))

    print("== extra: every non-square eps (claim says any non-square works) ==")
    for q in [3, 5, 7, 11, 13]:
        for eps in nonsquares(q):
            if eps == nonsquares(q)[0]:
                continue
            r = run(q, eps)
            print(json.dumps({k: r[k] for k in ("q", "eps", "z_total", "z_pass",
                                                  "global_bad", "valid")}))

    print("== negative control: eps = 1 (a square; E1, E2 then hyperbolic); expect failures ==")
    for q in [3, 5, 7]:
        r = run(q, 1)
        print(json.dumps({k: r[k] for k in ("q", "eps", "quadric_sizes", "z_total",
                                              "z_pass", "global_bad", "valid")}))

    total_pass = sum(r["z_pass"] for r in main_rows)
    total_z = sum(r["z_total"] for r in main_rows)
    all_valid = all(r["valid"] for r in main_rows)
    summary = {
        "score_pairs_passing": total_pass, "pairs_total": total_z,
        "valid": all_valid, "per_q": {r["q"]: [r["z_pass"], r["z_total"]] for r in main_rows},
        "quadric_sizes": {r["q"]: r["quadric_sizes"] for r in main_rows},
        "t_i_lines_not_through_x": {r["q"]: r["n_ti_notx"] for r in main_rows},
        "seconds": round(time.time() - t0, 1),
    }
    print("SUMMARY " + json.dumps(summary))


if __name__ == "__main__":
    main()
