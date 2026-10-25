"""For the f = 0 records: recover an alpha-closed connection set from the stored translate.

Usage: python3 s0_check.py            (reads recheck/orbit_check.log and recheck/orbit_check2.log)

An f = 0 solution file stores T, and orbit_check*.py found alpha and tau in T with alpha(T) tau = T. This program
solves alpha(s0) s0^-1 = tau for s0 in G = Q x Z_n (Q = SL(2,p), PSL(2,p) or a product of two such, p prime), and checks
that S = T s0 satisfies alpha(S) = S, with the cycle sizes stated in the records table (HAAR_D8_10.md §5.1, §2.6).

For alpha(x, z) = (g x g^-1, r z) the equation splits: g X g^-1 X^-1 = tau_Q in each matrix factor (up to sign in a
PSL factor), and (r - 1) z = tau_z mod n. In a matrix factor the X with g X = tau_Q X g form a linear subspace of
M_2(GF(p)), found by Gaussian elimination; the program enumerates that subspace and keeps det X = 1. If X0 is one
solution, the others are X0 C with C in the centraliser of g, so their number is |C_Q(g)|, which is printed alongside.

Its own arithmetic (prime fields only); it shares no code with the checkers or with orbit_check*.py. Like those, it is
a check of the search structure only and plays no role in the diameter checks.
"""
import itertools
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SOLS = os.path.join(HERE, "../../frontier/sols")


def mul(x, y, p):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p)


def inv(x, p):                     # determinant 1
    a, b, c, d = x
    return (d % p, -b % p, -c % p, a % p)


def key(x, p, psl):
    x = tuple(t % p for t in x)
    return min(x, tuple(-t % p for t in x)) if psl else x


def nullspace(rows, p):
    """basis of {v in GF(p)^4 : rows v = 0}"""
    rows = [list(r) for r in rows]
    piv, r = [], 0
    for col in range(4):
        i = next((i for i in range(r, len(rows)) if rows[i][col] % p), None)
        if i is None:
            continue
        rows[r], rows[i] = rows[i], rows[r]
        iv = pow(rows[r][col], p - 2, p)
        rows[r] = [v * iv % p for v in rows[r]]
        for j in range(len(rows)):
            if j != r and rows[j][col] % p:
                f = rows[j][col]
                rows[j] = [(u - f * v) % p for u, v in zip(rows[j], rows[r])]
        piv.append(col)
        r += 1
    basis = []
    for free in (c for c in range(4) if c not in piv):
        v = [0] * 4
        v[free] = 1
        for i, col in enumerate(piv):
            v[col] = -rows[i][free] % p
        basis.append(v)
    return basis


def solve_factor(g, t, p, psl):
    """all X of determinant 1 with g X g^-1 X^-1 = t (up to sign if psl), as canonical keys"""
    out = set()
    for sgn in ((1, -1) if psl else (1,)):
        tt = tuple(sgn * v % p for v in t)
        # the linear map X -> g X - tt X g on M_2 = GF(p)^4, X = (x0, x1, x2, x3) = [[x0, x1], [x2, x3]]
        cols = []
        for i in range(4):
            E = [0] * 4
            E[i] = 1
            lhs, rhs = mul(g, E, p), mul(mul(tt, E, p), g, p)
            cols.append([(u - v) % p for u, v in zip(lhs, rhs)])
        rows = [[cols[i][j] for i in range(4)] for j in range(4)]
        basis = nullspace(rows, p)
        for coef in itertools.product(range(p), repeat=len(basis)):
            X = tuple(sum(c * b[i] for c, b in zip(coef, basis)) % p for i in range(4))
            if (X[0] * X[3] - X[1] * X[2]) % p == 1:
                out.add(key(X, p, psl))
    return out


def parse_sol(path):
    lines = [ln for ln in open(path).read().split("\n") if ln.strip()]
    h = lines[0].split()
    d = int(h[0])
    if h[2] == "prod":
        facs = [(h[3], int(h[4])), (h[5], int(h[6]))]
        n = int(h[h.index("n") + 1])
    else:
        facs = [(h[2], int(h[3]))]
        n = int(h[5])
    T = []
    for ln in lines[1:1 + d]:
        ms = [tuple(map(int, m)) for m in re.findall(r"mat\((\d+),(\d+),(\d+),(\d+)\)", ln)]
        z = int(re.search(r"z=(\d+)", ln).group(1))
        assert len(ms) == len(facs)
        T.append((tuple(ms), z))
    return facs, n, T


def parse_logs():
    """(file, [g per factor], r, n, ([tau_Q per factor], tau_z), cycle sizes) for every log line with c != e"""
    out = []
    four = r"(\d+), (\d+), (\d+), (\d+)"
    for ln in open(os.path.join(HERE, "recheck/orbit_check.log")):
        m = re.match(rf"(\S+\.txt): .*conj by mat\({four}\) .*\(z -> (\d+)z mod (\d+)\), c = mat\({four}\) z=(\d+); "
                     r"cycle sizes of beta on S: \[([\d, ]+)\]", ln)
        if m:
            v = list(map(int, m.groups()[1:12]))
            out.append((m.group(1), [tuple(v[0:4])], v[4], v[5], ([tuple(v[6:10])], v[10]),
                        sorted(map(int, m.group(13).split(",")))))
    for ln in open(os.path.join(HERE, "recheck/orbit_check2.log")):
        m = re.match(rf"(\S+\.txt): .*conj by \('mat\({four}\)', 'mat\({four}\)'\) x \(z -> (\d+)z mod (\d+)\), "
                     rf"c = \(\(\({four}\), \({four}\)\), (\d+)\); cycle sizes of beta on S: \[([\d, ]+)\]", ln)
        if m:
            v = list(map(int, m.groups()[1:20]))
            out.append((m.group(1), [tuple(v[0:4]), tuple(v[4:8])], v[8], v[9],
                        ([tuple(v[10:14]), tuple(v[14:18])], v[18]), sorted(map(int, m.group(21).split(",")))))
    return out


def main():
    bad = 0
    for name, gs, r, n, (tq, tz), cyc_claim in parse_logs():
        facs, n2, T = parse_sol(os.path.join(SOLS, name))
        assert n2 == n and len(gs) == len(facs)
        psl = [kind == "psl" for kind, _ in facs]
        ps = [p for _, p in facs]

        def K(x):                       # canonical key of an element of G
            return tuple(key(m, p, s) for m, p, s in zip(x[0], ps, psl)), x[1] % n

        def alpha(x):
            return tuple(mul(mul(g, m, p), inv(g, p), p) for g, m, p in zip(gs, x[0], ps)), r * x[1] % n

        def gmul(x, y):
            return tuple(mul(a, b, p) for a, b, p in zip(x[0], y[0], ps)), (x[1] + y[1]) % n

        Tk = {K(t) for t in T}
        assert len(Tk) == len(T)
        # tau is in T, and alpha(T) tau = T (what orbit_check*.py reported)
        tau = (tuple(tq), tz)
        assert K(tau) in Tk and {K(gmul(alpha(t), tau)) for t in T} == Tk
        msols = [sorted(solve_factor(g, t, p, s)) for g, t, p, s in zip(gs, tq, ps, psl)]
        cents = [len(solve_factor(g, (1, 0, 0, 1), p, s)) for g, p, s in zip(gs, ps, psl)]
        zsols = [z for z in range(n) if (r - 1) * z % n == tz % n]
        nsol, good, cyc = 0, 0, None
        for ms in itertools.product(*msols):
            for z in zsols:
                s0 = (tuple(ms), z)
                nsol += 1
                # alpha(s0) s0^-1 = tau
                s0inv = (tuple(inv(m, p) for m, p in zip(s0[0], ps)), -z % n)
                assert K(gmul(alpha(s0), s0inv)) == K(tau)
                S = [gmul(t, s0) for t in T]
                Sk = {K(s): j for j, s in enumerate(S)}
                if {K(alpha(s)) for s in S} != set(Sk):
                    continue
                good += 1
                if cyc is None:
                    seen, cyc = set(), []
                    for j in range(len(S)):
                        if j in seen:
                            continue
                        L, cur = 0, S[j]
                        while Sk[K(cur)] not in seen:
                            seen.add(Sk[K(cur)])
                            L += 1
                            cur = alpha(cur)
                        cyc.append(L)
                    cyc.sort()
                    first = s0
        ok = nsol > 0 and good == nsol and cyc == cyc_claim
        bad += not ok
        print(f"{name}: {nsol} solutions s0 = {' x '.join(str(len(m)) for m in msols)} (matrix factors; |C(g)| = "
              f"{' x '.join(map(str, cents))}) x {len(zsols)} (Z_{n}); alpha(T s0) = T s0 for {good} of them; "
              f"cycle sizes of alpha on T s0: {cyc} (table: {cyc_claim}); "
              f"first s0 = {'; '.join('mat' + str(m) for m in first[0]) if good else '-'} z={first[1] if good else '-'}"
              f" -> {'OK' if ok else 'FAIL'}")
    print("ALL OK" if bad == 0 else f"{bad} FAILED")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
