r"""Checks for Section 3 of SYNTHETIC.tex (diameter 6: the hexagon, a Hermitian spread, whiskers).

H(q) is built from the coordinates of POLISHED.md \S6.1 (q = 2, 3); after that only incidence and
distances are used, except where the whisker formula of POLISHED.md Theorem 6.5 is evaluated (q = 3).

  1. H(q) is a generalized hexagon of order (q,q) (counts, diameter 6, every point on q+1 lines).
  2. The Hermitian spread S (lines of H(q) in the hyperplane Pi): q^3+1 pairwise opposite lines; every
     point of Pi on exactly one of them; every line not in S meets exactly one line of S.
  3. v in S; points at distance <= 3 from v; free points: q^3(q^2-1) of them; a line opposite v and
     not in S meets exactly one line of S, in a point not on v, and its other q points are free.
  4. An exact whisker set: q = 3 by the formula of POLISHED.md Theorem 6.5; q = 2 by exact-cover search.
  5. Delorme's levels: (L0), (L1), the components of A_0 (the ball of radius 2 about v, and the
     brooms), the counting identity q|A_0| + 2c = 2N with every outside element on exactly one element
     of A_0; the doubling (m = 2, 3 for q = 2; m = 2 for q = 3): count, max degree q+m, diameter 6.
  6. The sheets: for every word of length 3 the versions with prefix-compatible words form a copy of H(q).
  7. Theorem R (m = 2): the repeated lines, the deletion, a completion by anti-flags (found by a swap
     procedure), (q+2)-regular, diameter 6, 2(q+1)(q^4+q^3+q^2+4) elements.

Run: python3 check_d6.py
"""
import itertools
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from incidence import Structure, double_levels  # noqa: E402

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print('FAIL:', msg)


# ------------------------------------------------------------------ the split Cayley hexagon, q prime

def hexagon(q):
    def norm(v):
        i = next(i for i in range(7) if v[i] % q)
        c = pow(v[i], q - 2, q)
        return tuple((x * c) % q for x in v)

    def Qf(x):
        return (x[0] * x[4] + x[1] * x[5] + x[2] * x[6] - x[3] * x[3]) % q

    def B(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % q

    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and Qf(v) == 0:
            if norm(v) == v:
                pts.append(v)

    def tits(x, y):
        p = lambda i, j: (x[i] * y[j] - x[j] * y[i]) % q
        return (p(1, 2) == p(3, 4) and p(5, 4) == p(3, 2) and p(2, 0) == p(3, 5) and p(6, 5) == p(3, 0)
                and p(0, 1) == p(3, 6) and p(4, 6) == p(3, 1))
    lines = set()
    for x, y in itertools.combinations(pts, 2):
        if B(x, y) == 0 and tits(x, y):
            L = frozenset({x, y} | {norm(tuple((a * u + w) % q for u, w in zip(x, y))) for a in range(q)})
            lines.add(L)
    lines = sorted(lines, key=sorted)
    names = [('H', i) for i in range(len(lines))]
    S = Structure(pts, names, {(p, names[i]) for i, L in enumerate(lines) for p in L})
    return S, names, lines


def whiskers_formula(H, lines, names, q, c, c0, c1):
    """POLISHED.md Theorem 6.5 (q odd): W = { m in S_z \\ {v} : z != 0, nu(m cap Pi) = F(z) }."""
    inv = lambda z: pow(z % q, q - 2, q)
    v = frozenset(p for p in H.points if all(p[i] == 0 for i in (0, 2, 3, 4, 5)))
    W = set()
    for al in range(q):
        for be in range(q):
            if al == 0 and be == 0:
                continue
            for i, L in enumerate(lines):
                if L == v:
                    continue
                if all((x[0] + c * x[4] + al * x[2] + be * x[5]) % q == 0 for x in L):
                    X = [x for x in L if (x[0] + c * x[4]) % q == 0]
                    assert len(X) == 1
                    X = X[0]
                    num = (X[2] * X[3] - X[4] * X[5]) % q
                    den = (c * X[2] * X[2] + X[5] * X[5]) % q
                    nu = num * inv(den) % q
                    G = ((c0 * al + c1 * be) * (al * al + c * be * be) - be ** 3) % q
                    F = G * inv(al * al + c * be * be) % q
                    if nu == F:
                        W.add(names[i])
    return W


def exact_cover(universe, sets):
    """Return a list of keys whose sets partition universe (dict key -> frozenset), or None."""
    universe = set(universe)
    sol = []

    def rec(rem, avail):
        if not rem:
            return True
        x = min(rem, key=lambda z: sum(1 for k in avail if z in sets[k]))
        for k in [k for k in avail if x in sets[k]]:
            sol.append(k)
            if rec(rem - sets[k], [j for j in avail if not (sets[j] & sets[k])]):
                return True
            sol.pop()
        return False
    return sol if rec(universe, list(sets)) else None


def run(q, spread_hyperplane, whisker_mode, ms, full_R=True):
    tag = f'H({q})'
    H, names, lines = hexagon(q)
    N = (q + 1) * (q ** 4 + q * q + 1)
    check(len(H.points) == len(H.lines) == N, f'{tag}: N points and N lines')
    check(all(len(H.lines_on[p]) == q + 1 for p in H.points), f'{tag}: q+1 lines on each point')
    check(H.diameter() == 6, f'{tag}: diameter 6')
    v = next(L for i, L in enumerate(names) if all(p[i2] == 0 for p in lines[i] for i2 in (0, 2, 3, 4, 5)))
    dist_v = H.distances_from(v)

    # the Hermitian spread
    Spts = {p for p in H.points if spread_hyperplane(p)}
    S = [L for L in H.lines if H.pts_on[L] <= Spts]
    check(v in S and len(S) == q ** 3 + 1, f'{tag}: |S| = q^3+1, v in S')
    check(all(sum(1 for L in S if p in H.pts_on[L]) == 1 for p in Spts), f'{tag}: every point of Pi on one line of S')
    dS = {L: H.distances_from(L) for L in S}
    check(all(dS[L][M] == 6 for L, M in itertools.combinations(S, 2)), f'{tag}: lines of S pairwise opposite')
    Sset = set(S)
    for L in H.lines:
        if L not in Sset:
            meet = [M for M in S if H.pts_on[L] & H.pts_on[M]]
            check(len(meet) == 1, f'{tag}: a line not in S meets exactly one line of S')

    # free points and whiskers
    Pv = H.pts_on[v]
    Lv = [L for L in H.lines if L != v and H.pts_on[L] & Pv]
    check(len(Lv) == q * q + q, f'{tag}: q^2+q lines meet v')
    free = [p for p in H.points if p not in Spts and dist_v[p] == 5]
    check(len(free) == q ** 3 * (q * q - 1), f'{tag}: q^3(q^2-1) free points')
    near = [p for p in H.points if dist_v[p] <= 3]
    check(not (set(near) & Spts - Pv), f'{tag}: points at distance <= 3 from v in Pi lie on v')
    cand = [L for L in H.lines if dist_v[L] == 6 and L not in Sset]
    freeset = set(free)
    for L in cand:
        meet = [M for M in S if H.pts_on[L] & H.pts_on[M]]
        P = H.pts_on[L]
        check(len(meet) == 1 and meet[0] != v and len(P & Spts) == 1 and len(P & freeset) == q,
              f'{tag}: a line opposite v not in S has one point in Pi (not on v) and q free points')
    if whisker_mode[0] == 'formula':
        W = whiskers_formula(H, lines, names, q, *whisker_mode[1:])
    else:
        sol = exact_cover(freeset, {L: frozenset(H.pts_on[L] & freeset) for L in cand})
        W = set(sol)
    check(len(W) == q * q * (q * q - 1), f'{tag}: |W| = q^2(q^2-1)')
    check(all(sum(1 for L in W if p in H.pts_on[L]) == 1 for p in free), f'{tag}: W is an exact whisker set')
    check(all(L in set(cand) for L in W), f'{tag}: whiskers are opposite v and not in S')

    # Delorme's levels
    level = {}
    for x in [*Sset, *Spts, *Lv, *W]:
        level[x] = 0
    for x in [*Sset, *Pv]:
        level[x] = 1
    level[v] = 2
    A0 = set(level)
    A1 = {x for x in level if level[x] >= 1}
    check(len(A1) == q ** 3 + q + 2, f'{tag}: |A_1| = q^3+q+2')
    check(len(A0) == q ** 4 + 2 * q ** 3 + q * q + 2 * q + 2 + len(W), f'{tag}: |A_0|')
    # (L0) and (L1)
    allel = list(H.points) + list(H.lines)
    nb = lambda x: H.lines_on[x] if x in H.lines_on and x not in H.pts_on else H.pts_on[x]
    for x in allel:
        k = level.get(x, -1)
        nbs = nb(x)
        if k == -1:
            check(sum(1 for y in nbs if y in A0) == 1, f'{tag}: (L0) with equality: outside element sees exactly one element of A_0')
        else:
            higher = [y for y in nbs if level.get(y, -1) == k + 1]
            check(len(higher) <= 1, f'{tag}: (L1) at most one neighbour one level up')
            check(all(level.get(y, -1) >= k - 1 for y in nbs) or k == 0, f'{tag}: (L1) neighbours of A_k lie in A_(k-1)')
    for x in allel:
        if level.get(x, -1) >= 1:
            check(all(y in A0 for y in nb(x)), f'{tag}: neighbours of A_1 lie in A_0')
        if level.get(x, -1) == 2:
            check(all(level.get(y, -1) >= 1 for y in nb(x)), f'{tag}: neighbours of A_2 lie in A_1')
    # components of A_0: trees of diameter <= 4: the ball of radius 2 about v, and q^3 brooms
    comp = []
    seen = set()
    for x in A0:
        if x in seen:
            continue
        c = {x}
        st = [x]
        while st:
            y = st.pop()
            for z in nb(y):
                if z in A0 and z not in c:
                    c.add(z)
                    st.append(z)
        seen |= c
        comp.append(c)
    check(len(comp) == q ** 3 + 1, f'{tag}: q^3+1 components of A_0')
    ball = {v} | Pv | set(Lv)
    check(any(c == ball for c in comp), f'{tag}: one component is the ball of radius 2 about v')
    for c in comp:
        edges = sum(1 for y in c for z in nb(y) if z in c) // 2
        check(edges == len(c) - 1, f'{tag}: components are trees')
        if c != ball:
            ls = [y for y in c if y in Sset]
            check(len(ls) == 1, f'{tag}: a broom has one spread line')
            n0 = ls[0]
            check(c == {n0} | H.pts_on[n0] | {L for L in W if H.pts_on[L] & H.pts_on[n0]}, f'{tag}: broom = line, its points, whiskers')
    check(q * len(A0) + 2 * len(comp) == 2 * N, f'{tag}: counting bound q|A_0| + 2c = 2N attained')

    for m in ms:
        D = double_levels(H, level, m)
        n = len(D.points) + len(D.lines)
        exp = 2 * N + (m - 1) * (q ** 4 + 2 * q ** 3 + q * q + 2 * q + 2 + len(W) + m * (q ** 3 + q + 2) + m * m)
        check(n == exp, f'{tag}: doubled count, m={m}')
        md = max(max(D.point_degree(x) for x in D.points), max(D.line_degree(L) for L in D.lines))
        check(md == q + m, f'{tag}: doubled max degree q+m, m={m}')
        check(D.diameter() == 6, f'{tag}: doubled diameter 6, m={m}')
        # the table of versions in SYNTHETIC.tex 3.3: every version's neighbourhood
        Lvset, Wset, Sv = set(Lv), set(W), Sset - {v}
        words = lambda k: list(itertools.product(range(m), repeat=k))
        nbD = lambda x: D.lines_on[x] if x in D.lines_on and x not in D.pts_on else D.pts_on[x]
        def vers(x):
            return [(x, w) for w in words(level.get(x, -1) + 1)]
        for w in words(3):
            check(nbD((v, w)) == {(p, w[:2]) for p in Pv}, f'{tag}: table row v')
        for p in Pv:
            for w in words(2):
                exp = {(v, w + (k,)) for k in range(m)} | {(L, w[:1]) for L in H.lines_on[p] if L != v}
                check(nbD((p, w)) == exp, f'{tag}: table row point of v')
        for n0 in Sv:
            for w in words(2):
                check(nbD((n0, w)) == {(p, w[:1]) for p in H.pts_on[n0]}, f'{tag}: table row spread line')
        for p in Spts - Pv:
            n0 = next(L for L in H.lines_on[p] if L in Sset)
            for w in words(1):
                exp = ({(n0, w + (k,)) for k in range(m)} | {(h, w) for h in H.lines_on[p] if h in Wset}
                       | {(L, ()) for L in H.lines_on[p] if L not in Sset and L not in Wset})
                check(nbD((p, w)) == exp, f'{tag}: table row point of Pi')
        for L in Lvset:
            p0 = next(iter(H.pts_on[L] & Pv))
            for w in words(1):
                check(nbD((L, w)) == {(p0, w + (k,)) for k in range(m)} | {(x, ()) for x in H.pts_on[L] - {p0}}, f'{tag}: table row line meeting v')
        for h in Wset:
            p0 = next(iter(H.pts_on[h] & Spts))
            for w in words(1):
                check(nbD((h, w)) == {(p0, w)} | {(x, ()) for x in H.pts_on[h] - {p0}}, f'{tag}: table row whisker')
        for r_ in H.points:
            if level.get(r_, -1) == -1:
                a0 = [L for L in H.lines_on[r_] if L in A0]
                check(len(a0) == 1 and nbD((r_, ())) == set(vers(a0[0])) | {(L, ()) for L in H.lines_on[r_] if L not in A0}, f'{tag}: table row outside point')
        for N_ in H.lines:
            if level.get(N_, -1) == -1:
                a0 = [x for x in H.pts_on[N_] if x in A0]
                check(len(a0) == 1 and level[a0[0]] == 0 and nbD((N_, ())) == set(vers(a0[0])) | {(x, ()) for x in H.pts_on[N_] if x not in A0}, f'{tag}: table row outside line')
        if m == 2:
            # sheets
            for omega in itertools.product(range(m), repeat=3):
                def ok(w):
                    return tuple(omega[:len(w)]) == w
                sp = [x for x in D.points if ok(x[1])]
                sl = [x for x in D.lines if ok(x[1])]
                check(len(sp) == len(sl) == N, f'{tag}: a sheet has N points and N lines')
                fl = {(a[0], b[0]) for a, b in D.flags if ok(a[1]) and ok(b[1])}
                check(fl == H.flags, f'{tag}: a sheet is a copy of H(q)')
            if full_R:
                theorem_R(H, D, v, S, Pv, W, q, m, tag)
    return H


def theorem_R(H, D, v, S, Pv, W, q, m, tag):
    # repeated lines
    cls = {}
    for L in D.lines:
        cls.setdefault(frozenset(D.pts_on[L]), []).append(L)
    rep = [c for c in cls.values() if len(c) > 1]
    check(len(rep) == m * q ** 3 + m * m and all(len(c) == m for c in rep), f'{tag}: mq^3+m^2 classes of m repeated lines')
    Sv = [L for L in S if L != v]
    R = set(Sv[:q])
    delete = set()
    for L in D.lines:
        x, w = L
        if x == v and w[2] >= 1:
            delete.add(L)
        if x in set(Sv) and x not in R and w[1] >= 1:
            delete.add(L)
    check(len(delete) == (m - 1) * m * (q ** 3 - q + m), f'{tag}: deleted lines = the excess')
    lines2 = [L for L in D.lines if L not in delete]
    flags2 = {(p, L) for p, L in D.flags if L not in delete}
    E = Structure(D.points, lines2, flags2)
    check(len(E.points) == len(E.lines), f'{tag}: after deletion, as many points as lines')
    Delta = q + m
    defp = {p: Delta - E.point_degree(p) for p in E.points}
    defl = {L: Delta - E.line_degree(L) for L in E.lines}
    check(max(defp.values()) <= m - 1 and max(defl.values()) <= m - 1 and min(defp.values()) >= 0, f'{tag}: deficits <= m-1')
    check(sum(defp.values()) == sum(defl.values()), f'{tag}: deficit sums agree')
    # completion by anti-flags (swap procedure, Lemma 7.2)
    rng = random.Random(5)
    P = [p for p in E.points for _ in range(defp[p])]
    Ls = [L for L in E.lines for _ in range(defl[L])]
    rng.shuffle(Ls)
    J = list(zip(P, Ls))

    def bad(i):
        p, L = J[i]
        return (p, L) in flags2 or sum(1 for j in range(len(J)) if J[j] == (p, L)) > 1
    for it in range(200000):
        badi = [i for i in range(len(J)) if (J[i][0], J[i][1]) in flags2]
        cnt = {}
        for e in J:
            cnt[e] = cnt.get(e, 0) + 1
        badi += [i for i in range(len(J)) if cnt[J[i]] > 1]
        if not badi:
            break
        i = rng.choice(badi)
        j = rng.randrange(len(J))
        (p, L), (p2, L2) = J[i], J[j]
        J[i], J[j] = (p, L2), (p2, L)
    Jset = set(J)
    check(len(Jset) == len(J) and not (Jset & flags2), f'{tag}: completion by distinct anti-flags found')
    F = Structure(E.points, E.lines, flags2 | Jset)
    degs = {F.point_degree(p) for p in F.points} | {F.line_degree(L) for L in F.lines}
    check(degs == {Delta}, f'{tag}: Theorem R structure is (q+m)-regular')
    n = len(F.points) + len(F.lines)
    check(n == 2 * (q + 1) * (q ** 4 + q * q + 1 + (m - 1) * (q ** 3 + m + 1)), f'{tag}: Theorem R count')
    check(E.diameter() == 6 and F.diameter() == 6, f'{tag}: Theorem R diameter 6 (before and after completion)')


def main():
    # q = 3: Pi: X0 + c X4 = 0 with -c a non-square (c = 1); whisker formula with (c0, c1) = (1, 2)
    run(3, lambda p: (p[0] + 1 * p[4]) % 3 == 0, ('formula', 1, 1, 2), ms=(2,))
    print('H(3): spread, free points, exact whiskers (formula), levels, doubling m = 2, sheets, Theorem R: checked')
    # q = 2: Pi: X3 = X0 + X4 + ... (delta = 1, Tr(1) = 1 in GF(2)); whiskers by exact cover
    run(2, lambda p: (p[3] + p[0] + p[4]) % 2 == 0, ('search',), ms=(2, 3))
    print('H(2): spread, free points, exact whiskers (search), levels, doubling m = 2, 3, sheets, Theorem R: checked')
    print('ALL CHECKS PASSED' if not FAIL else f'{len(FAIL)} FAILURES')
    return not FAIL


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
