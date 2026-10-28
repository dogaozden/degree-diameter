r"""Checks for Section 2 of SYNTHETIC.tex (diameter 4: clones and shadow lines in generalized
quadrangles).

  1. W(3,q) (q = 3, 5) is a GQ of order (q,q).
  2. Theorem B on random data: random weights, random multisets of shadow lines with random
     stand-ins, on W(3,3) and on AS(3): diameter 4, the degree formulas, and two non-collinear old
     points stay non-collinear.
  3. AS(q) built from W(q) by Payne derivation, using only incidence (q = 3, 5, 7): a GQ of order
     (q-1, q+1) whose hyperbolic lines form a spread.  The two elliptic quadrics of Theorem A
     (POLISHED.md \S4): each meets every hyperbolic line once, together they meet every line twice,
     they share exactly one point; the clone structure is (q+2)-regular, has diameter 4 and
     2q^2(q+2) elements.
  4. Proposition C / Corollary C1 (q = 3, 5), in the cyclic model of research/theorems/polish/c1w3.py:
     the 2-ovoid meets every line in 2 points, the spread, the structure with clones of the 2-ovoid
     and two shadow lines over each spread line, its explicit regular completion: (q+3)-regular,
     diameter 4, 2(q^2+1)(q+3) elements.
  5. Delorme's doubling at D = 4 (a spread and one of its lines with its points) on W(3,3), m = 2, 3.
  6. q even: W(3,2) with an ovoid and a spread, j = 1, 2.
  7. The (7,4) example: Q(4,5), one clone of each point of an ovoid, 21 shadow lines with stand-ins
     (data research/theorems/polish/q4_359_lines.json from branch claude/thm-polish-2oddll, copied here).

Run: python3 check_d4.py
"""
import itertools
import json
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from incidence import Structure, is_gq, symplectic_W3, payne_derivation, double_levels  # noqa: E402

FAIL = []


def check(cond, msg):
    if not cond:
        FAIL.append(msg)
        print('FAIL:', msg)


# ------------------------------------------------------------------ clones and shadow lines

def clones_shadows(S, w, M, standin=None):
    """w: dict point -> number of clones; M: list of old lines (a multiset); standin[(mu, p)] in
    {p, (p,'c',1), ..., (p,'c',w(p))} (default: p).  Clone (p,'c',i) is on every old line through p;
    shadow line ('sh', mu) contains standin[(mu, p)] for each point p of M[mu]."""
    pts = list(S.points) + [(p, 'c', i) for p in S.points for i in range(1, w.get(p, 0) + 1)]
    lns = list(S.lines) + [('sh', mu) for mu in range(len(M))]
    flags = set(S.flags)
    for p in S.points:
        for i in range(1, w.get(p, 0) + 1):
            for L in S.lines_on[p]:
                flags.add(((p, 'c', i), L))
    for mu, L in enumerate(M):
        for p in S.pts_on[L]:
            x = standin.get((mu, p), p) if standin else p
            flags.add((x, ('sh', mu)))
    return Structure(pts, lns, flags)


def check_theorem_B(S, s, t, trials, rng, tag):
    for trial in range(trials):
        w = {p: rng.choice([0, 0, 0, 1, 2]) for p in S.points}
        M = [rng.choice(S.lines) for _ in range(rng.randrange(0, len(S.lines)))]
        standin = {}
        for mu, L in enumerate(M):
            for p in S.pts_on[L]:
                standin[(mu, p)] = rng.choice([p] + [(p, 'c', i) for i in range(1, w[p] + 1)])
        T = clones_shadows(S, w, M, standin)
        check(T.diameter() == 4, f'{tag}: Theorem B diameter 4 (trial {trial})')
        # degree formulas
        for L in S.lines:
            check(T.line_degree(L) == s + 1 + sum(w[p] for p in S.pts_on[L]), f'{tag}: old line degree')
        for mu in range(len(M)):
            check(T.line_degree(('sh', mu)) == s + 1, f'{tag}: shadow line degree')
        serve = {}
        for (mu, p), x in standin.items():
            serve[x] = serve.get(x, 0) + 1
        for x in T.points:
            base = t + 1
            check(T.point_degree(x) == base + serve.get(x, 0), f'{tag}: point/clone degree')
        # non-collinear old points stay non-collinear
        for u, v in itertools.combinations(S.points[:12], 2):
            if not S.collinear(u, v):
                check(not T.collinear(u, v), f'{tag}: non-collinear old points stay non-collinear')


# ------------------------------------------------------------------ AS(q) and Theorem A

def theorem_A(q):
    W, b = symplectic_W3(q)
    check(is_gq(W, q, q), f'W(3,{q}) is a GQ')
    x = (1, 0, 0, 0)
    AS = payne_derivation(W, x)
    check(len(AS.points) == q ** 3 and len(AS.lines) == q * q * (q + 2), f'AS({q}) counts')
    check(is_gq(AS, q - 1, q + 1), f'AS({q}) is a GQ of order (q-1,q+1)')
    hyp = [L for L in AS.lines if L[0] == 'hyp']
    check(len(hyp) == q * q and all(sum(1 for L in hyp if p in AS.pts_on[L]) == 1 for p in AS.points),
          f'AS({q}): the hyperbolic lines form a spread')

    # the two elliptic quadrics 2 X0 X1 = X2^2 - eps X3^2 and 2 eps X0 X1 = X2^2 - eps X3^2 (minus x)
    squares = {(z * z) % q for z in range(1, q)}
    eps = next(e for e in range(1, q) if e not in squares)
    inv = lambda z: pow(z, q - 2, q)
    k1, k2 = inv(2), inv(2 * eps % q)

    def norm(v):
        i = next(i for i in range(4) if v[i] % q)
        c = inv(v[i])
        return tuple((y * c) % q for y in v)

    def quadric(k):
        return {norm(((k * ((bb * bb - eps * cc * cc) % q)) % q, 1, bb, cc)) for bb in range(q) for cc in range(q)}
    E1, E2 = quadric(k1), quadric(k2)
    check(len(E1) == len(E2) == q * q and E1 <= set(AS.points) and E2 <= set(AS.points), f'AS({q}): |E_i| = q^2')
    check(len(E1 & E2) == 1, f'AS({q}): E_1 and E_2 share exactly one point')
    for L in AS.lines:
        P = AS.pts_on[L]
        check(len(P & E1) + len(P & E2) == 2, f'AS({q}): every line meets E_1, E_2 twice in total')
        if L[0] == 'hyp':
            check(len(P & E1) == 1 and len(P & E2) == 1, f'AS({q}): hyperbolic line meets each E_i once')
    w = {p: (p in E1) + (p in E2) for p in AS.points}
    T = clones_shadows(AS, w, [])
    degs = {T.point_degree(p) for p in T.points} | {T.line_degree(L) for L in T.lines}
    check(degs == {q + 2}, f'AS({q}) + clones of E_1, E_2: (q+2)-regular')
    check(len(T.points) + len(T.lines) == 2 * q * q * (q + 2), f'AS({q}) + clones: 2q^2(q+2) elements')
    if q <= 5:
        check(T.diameter() == 4, f'AS({q}) + clones: diameter 4')
    return AS


# ------------------------------------------------------------------ the cyclic model of W(3,q): 2-ovoid and spread

def cyclic_W3(p):
    """As in research/theorems/polish/c1w3.py: PG(3,p) = E*/F*, E = GF(p^4), W(3,p) for
    b(x,y) = Tr(d x y^{p^2}), d = g^{(p^2+1)/2}.  Returns (W, O, spread)."""
    q = p

    def polymulmod(a, bb, mod):
        r = [0] * 7
        for i in range(4):
            for j in range(4):
                r[i + j] = (r[i + j] + a[i] * bb[j]) % p
        for k in range(6, 3, -1):
            c = r[k]
            if c:
                for t in range(5):
                    r[k - 4 + t] = (r[k - 4 + t] - c * mod[t]) % p
        return tuple(r[:4])

    def find_prim():
        for c in itertools.product(range(p), repeat=4):
            mod = list(c) + [1]
            if c[0] == 0:
                continue
            e = (1, 0, 0, 0)
            cur = e
            for k in range(1, p ** 4):
                cur = polymulmod(cur, (0, 1, 0, 0), mod)
                if cur == e:
                    break
            if k == p ** 4 - 1:
                return mod
    mod = find_prim()
    Q4 = p ** 4
    pw = [(1, 0, 0, 0)]
    for k in range(1, Q4 - 1):
        pw.append(polymulmod(pw[-1], (0, 1, 0, 0), mod))
    Nn = (q ** 4 - 1) // (q - 1)

    def norm(v):
        for c in v:
            if c:
                iv = pow(c, p - 2, p)
                return tuple((x * iv) % p for x in v)
    pt = {}
    ptv = []
    for i in range(Nn):
        pt[norm(pw[i])] = i
        ptv.append(pw[i])

    def tr(j):
        s = [0, 0, 0, 0]
        for e in range(4):
            v = pw[(j * q ** e) % (Q4 - 1)]
            s = [(a + bb) % p for a, bb in zip(s, v)]
        return s[0]
    dexp = (q * q + 1) // 2
    lines = set()
    for i in range(Nn):
        for k in range(Nn):
            if k != i and tr(dexp + i + k * q * q) == 0:
                L = {i, k}
                for t in range(p):
                    L.add(pt[norm(tuple((a * t + bb) % p for a, bb in zip(ptv[i], ptv[k])))])
                lines.add(frozenset(L))
    lines = sorted(lines, key=sorted)
    names = [('C', j) for j in range(len(lines))]
    W = Structure(list(range(Nn)), names, {(x, names[j]) for j, L in enumerate(lines) for x in L})
    O = {i for i in range(Nn) if i % (q + 1) in (0, q)}
    K = q * q + 1
    sp = {frozenset((i + K * k) % Nn for k in range(q + 1)) for i in range(Nn)}
    lid = {L: names[j] for j, L in enumerate(lines)}
    spread = [lid[s] for s in sp]
    return W, O, spread


def corollary_C1(q):
    W, O, spread = cyclic_W3(q)
    check(is_gq(W, q, q), f'cyclic W(3,{q}) is a GQ')
    check(all(len(W.pts_on[L] & O) == 2 for L in W.lines), f'W(3,{q}): O is a 2-ovoid')
    check(len(spread) == q * q + 1 and all(sum(1 for L in spread if x in W.pts_on[L]) == 1 for x in W.points),
          f'W(3,{q}): spread')
    w = {x: 1 for x in O}
    M = [L for L in spread for _ in range(2)]
    T = clones_shadows(W, w, M)
    for x in W.points:
        check(T.point_degree(x) == q + 3, f'C1 q={q}: old point degree q+3')
    for L in W.lines:
        check(T.line_degree(L) == q + 3, f'C1 q={q}: old line degree q+3')
    clones = [x for x in T.points if isinstance(x, tuple) and x[1] == 'c']
    shadows = [L for L in T.lines if L[0] == 'sh']
    check(all(T.point_degree(c) == q + 1 for c in clones) and all(T.line_degree(L) == q + 1 for L in shadows),
          f'C1 q={q}: clones and shadow lines have degree q+1')
    check(len(T.points) + len(T.lines) == 2 * (q * q + 1) * (q + 3), f'C1 q={q}: 2(q^2+1)(q+3) elements')
    # explicit completion: clone c_i joined to shadow lines y_{2i}, y_{2i+1} (indices mod 2(q^2+1))
    b = len(shadows)
    extra = set()
    for i, c in enumerate(clones):
        for k in (0, 1):
            extra.add((c, shadows[(2 * i + k) % b]))
    check(not (extra & T.flags), f'C1 q={q}: completing pairs are anti-flags')
    R = Structure(T.points, T.lines, T.flags | extra)
    degs = {R.point_degree(x) for x in R.points} | {R.line_degree(L) for L in R.lines}
    check(degs == {q + 3}, f'C1 q={q}: completion is (q+3)-regular')
    check(T.diameter() == 4 and R.diameter() == 4, f'C1 q={q}: diameter 4')
    return W, spread


def delorme_d4(W, spread, q):
    v = spread[0]
    for m in (2, 3):
        level = {L: 0 for L in spread}
        level[v] = 1
        for p in W.pts_on[v]:
            level[p] = 0
        D = double_levels(W, level, m)
        n = len(D.points) + len(D.lines)
        check(n == 2 * (q + 1) * (q * q + 1) + (m - 1) * ((q * q + 1) + (q + 1) + m), f'Delorme D=4 count, m={m}')
        md = max(max(D.point_degree(x) for x in D.points), max(D.line_degree(L) for L in D.lines))
        check(md == q + m, f'Delorme D=4 max degree q+m, m={m}')
        check(D.diameter() == 4, f'Delorme D=4 diameter 4, m={m}')


def even_q2():
    """W(3,2): an ovoid and a spread (found by exhaustive search), j = 1, 2 copies."""
    W, b = symplectic_W3(2)
    check(is_gq(W, 2, 2), 'W(3,2) is a GQ')
    pts = W.points

    def exact(cover_sets, universe):
        # tiny exact-cover search
        universe = set(universe)
        sol = []

        def rec(rem, avail):
            if not rem:
                return True
            x = min(rem, key=lambda z: sum(1 for c in avail if z in c))
            for c in [c for c in avail if x in c]:
                sol.append(c)
                if rec(rem - c, [d for d in avail if not (d & c)]):
                    return True
                sol.pop()
            return False
        return sol if rec(universe, cover_sets) else None
    # spread: lines partitioning the points
    sp = exact([frozenset(W.pts_on[L]) for L in W.lines], pts)
    spread = [L for L in W.lines if frozenset(W.pts_on[L]) in sp]
    # ovoid: points meeting every line once = exact cover of the lines by the point pencils
    ov = exact([frozenset(W.lines_on[p]) for p in pts], W.lines)
    O = [p for p in pts if frozenset(W.lines_on[p]) in ov]
    check(len(spread) == 5 and len(O) == 5, 'W(3,2): spread and ovoid of size q^2+1')
    for j in (1, 2):
        T = clones_shadows(W, {p: j for p in O}, [L for L in spread for _ in range(j)])
        for x in W.points:
            check(T.point_degree(x) == 3 + j, 'even: old point degree')
        for L in W.lines:
            check(T.line_degree(L) == 3 + j, 'even: old line degree')
        check(len(T.points) + len(T.lines) == 2 * (3 + j) * 5, 'even: 2 Delta (q^2+1) elements')
        check(T.diameter() == 4, 'even: diameter 4')


def example_359():
    sys.path.insert(0, str(HERE.parents[1] / 'gq4'))
    from gq_clones import q4
    q = 5
    pts, lines, ovoid = q4(q)
    data = json.load(open(HERE / 'q4_359_lines.json'))
    idx = {tuple(p): i for i, p in enumerate(pts)}
    O = set(ovoid)
    S = Structure(list(range(len(pts))), [('Q', j) for j in range(len(lines))],
                  {(x, ('Q', j)) for j, L in enumerate(lines) for x in L})
    check(is_gq(S, q, q), 'Q(4,5) is a GQ')
    check(all(len(S.pts_on[L] & O) == 1 for L in S.lines), 'Q(4,5): ovoid')
    lid = {frozenset(L): ('Q', j) for j, L in enumerate(lines)}
    M, standin = [], {}
    for mu, e in enumerate(data):
        L = lid[frozenset(idx[tuple(p)] for p in e['line'])]
        M.append(L)
        cl = {idx[tuple(p)] for p in e['clone_standins']}
        for x in S.pts_on[L]:
            standin[(mu, x)] = (x, 'c', 1) if x in cl else x
    w = {x: 1 for x in O}
    T = clones_shadows(S, w, M, standin)
    n = len(T.points) + len(T.lines)
    md = max(max(T.point_degree(x) for x in T.points), max(T.line_degree(L) for L in T.lines))
    check(len(M) == 21 and n == 359 and md == 7, 'the (7,4) example: 21 shadow lines, 359 elements, max degree 7')
    serve = {}
    for x in standin.values():
        serve[x] = serve.get(x, 0) + 1
    check(max(serve.values()) == 1, 'the (7,4) example: every point and clone stands in for at most one shadow line')
    check(all(standin[(mu, x)] == x or x in O for (mu, x) in standin), 'stand-ins are clones of ovoid points only')
    twice = [x for x in O if sum(1 for L in M if x in S.pts_on[L]) == 2]
    check(len(twice) >= 1, 'some ovoid point is on two shadow lines (needs its clone as stand-in)')
    check(T.diameter() == 4, 'the (7,4) example: diameter 4')
    return len(twice)


def main():
    rng = random.Random(3)
    W3, _ = symplectic_W3(3)
    check(is_gq(W3, 3, 3), 'W(3,3) GQ')
    W5, _ = symplectic_W3(5)
    check(is_gq(W5, 5, 5), 'W(3,5) GQ')
    print('W(3,3), W(3,5): GQs of order (q,q)')
    check_theorem_B(W3, 3, 3, 6, rng, 'W(3,3)')
    AS3 = theorem_A(3)
    check_theorem_B(AS3, 2, 4, 6, rng, 'AS(3)')
    print('Theorem B: random weights, multisets and stand-ins on W(3,3) and AS(3): checked')
    for q in (5, 7):
        theorem_A(q)
    print('AS(q) by Payne derivation and Theorem A: checked for q = 3, 5, 7 (diameter for q = 3, 5)')
    Wc, spread = corollary_C1(3)
    corollary_C1(5)
    print('Proposition C / Corollary C1: checked for q = 3, 5')
    delorme_d4(Wc, spread, 3)
    print("Delorme's doubling at D = 4 on W(3,3), m = 2, 3: checked")
    even_q2()
    print('W(3,2) with an ovoid and a spread, j = 1, 2: checked')
    t = example_359()
    print(f'the (7,4) example on Q(4,5): checked ({t} ovoid points on two shadow lines)')
    print('ALL CHECKS PASSED' if not FAIL else f'{len(FAIL)} FAILURES')
    return not FAIL


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
