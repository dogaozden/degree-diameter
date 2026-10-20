r"""The Araujo-Pardo--Lopez (AL) graph and the four-hat (+2) graph, built ONLY from the
coordinate description in coords.tex (no import of construction.py or lib.py).

Coordinates.  F = GF(q).  Points (x:y:z), lines [u:v:w], incidence ux+vy+wz = 0.
    ell = [1:0:0]  (x = 0)              A = (1:0:0)
    X_t = (0:t:1), t in F;  P = (0:1:0)  (the q+1 points of ell)
    lam_t = [0:1:-t], t in F;  lam_inf = [0:0:1]  (the q+1 lines through A; X_t is on lam_t, P on lam_inf)
AL:   S = {0,1,a};  a in F \ {0,1}.
4hat: S = {0,1,a,c}; c in F \ {0,1,a};  T = {0,1,c};  sigma = (0 c 1): 0->c, c->1, 1->0.

Each structure is built three ways that must agree:
    by_rules        -- the numbered construction steps (plane, minus, plus);
    by_point_table  -- the neighbour set of every point, as a formula;
    by_line_table   -- the neighbour set of every line, as a formula.
filler(): the matching p -- delta(p), delta(x:y:z) = [x:z:-y], on the points of degree q+1.

Run: python coords.py            (all checks for q = 4..13; prints a table)
"""
import itertools
import sys


# ------------------------------------------------------------------ GF(q), from scratch

def prime_power(q):
    for p in range(2, q + 1):
        if q % p == 0:
            k, r = 0, q
            while r % p == 0:
                r //= p
                k += 1
            return (p, k) if r == 1 else None
    return None


class GF:
    """GF(p^k); element = integer whose base-p digits are polynomial coefficients (low first)."""

    def __init__(self, q):
        self.q = q
        self.p, self.k = prime_power(q)
        self.mod = self._irreducible() if self.k > 1 else None
        els = range(q)
        self._mul = [[self._mul_slow(x, y) for y in els] for x in els]
        self._add = [[self._add_slow(x, y) for y in els] for x in els]
        self._neg = [next(y for y in els if self._add[x][y] == 0) for x in els]
        self._inv = [None] + [next(y for y in els if self._mul[x][y] == 1) for x in range(1, q)]
        assert all(self._mul[x][self._inv[x]] == 1 for x in range(1, q))

    def _digits(self, x):
        return [(x // self.p ** i) % self.p for i in range(self.k)]

    def _from(self, d):
        return sum(c * self.p ** i for i, c in enumerate(d))

    def _add_slow(self, x, y):
        return self._from([(a + b) % self.p for a, b in zip(self._digits(x), self._digits(y))])

    def _polymulmod(self, a, b, f):
        p, k = self.p, self.k
        prod = [0] * (2 * k - 1)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                prod[i + j] = (prod[i + j] + x * y) % p
        for i in range(len(prod) - 1, k - 1, -1):        # f monic of degree k: x^k = -f[0..k-1]
            c = prod[i]
            if c:
                prod[i] = 0
                for j in range(k):
                    prod[i - k + j] = (prod[i - k + j] - c * f[j]) % p
        return prod[:k]

    def _irreducible(self):
        p, k = self.p, self.k
        for tail in itertools.product(range(p), repeat=k):  # f = x^k + tail
            f = list(tail)
            if f[0] == 0:
                continue
            # irreducible iff no root-free factorisation: check x^(p^k) = x and gcd conditions;
            # small k (<= 3 here) => irreducible iff no factor of degree <= k/2; brute force by
            # checking the multiplicative group generated has order p^k - 1 for some element.
            self.mod = f
            elems = [list(d) for d in itertools.product(range(p), repeat=k)]
            nonzero = [e for e in elems if any(e)]
            ok = True
            for e in nonzero:                               # every nonzero element invertible?
                if not any(self._polymulmod(e, g, f) == [1] + [0] * (k - 1) for g in nonzero):
                    ok = False
                    break
            if ok:
                return f
        raise ValueError('no irreducible polynomial')

    def _mul_slow(self, x, y):
        if self.k == 1:
            return (x * y) % self.p
        return self._from(self._polymulmod(self._digits(x), self._digits(y), self.mod))

    def add(self, x, y): return self._add[x][y]
    def mul(self, x, y): return self._mul[x][y]
    def neg(self, x): return self._neg[x]
    def sub(self, x, y): return self._add[x][self._neg[y]]
    def inv(self, x): return self._inv[x]


def normalize(F, v):
    """Scale a nonzero triple so its first nonzero coordinate is 1."""
    i = next(i for i in range(3) if v[i])
    s = F.inv(v[i])
    return tuple(F.mul(s, t) for t in v)


def dot(F, p, L):
    return F.add(F.add(F.mul(p[0], L[0]), F.mul(p[1], L[1])), F.mul(p[2], L[2]))


# ------------------------------------------------------------------ the frame

class Frame:
    def __init__(self, q, a, c=None):
        F = self.F = GF(q)
        self.q, self.a, self.c = q, a, c
        assert a not in (0, 1) and a < q
        self.four = c is not None
        if self.four:
            assert c not in (0, 1, a) and c < q
            self.S = (0, 1, a, c)
            self.T = (0, 1, c)
            self.sigma = {0: c, c: 1, 1: 0}
            self.sigma_inv = {v: k for k, v in self.sigma.items()}
        else:
            self.S = (0, 1, a)
            self.T = (0, 1)             # AL: X_0, X_1 not on M; no rotation
        self.els = list(range(q))
        n = lambda v: ('pt', normalize(F, v))
        m = lambda v: ('ln', normalize(F, v))
        self.pt, self.ln = n, m
        self.A, self.P = n((1, 0, 0)), n((0, 1, 0))
        self.ell, self.lam_inf = m((1, 0, 0)), m((0, 0, 1))
        self.X = lambda t: n((0, t, 1))
        self.lam = lambda t: m((0, 1, F.neg(t)))
        self.points = sorted({n(v) for v in itertools.product(self.els, repeat=3) if any(v)})
        self.lines = sorted({m(v) for v in itertools.product(self.els, repeat=3) if any(v)})
        assert len(self.points) == q * q + q + 1
        self.new_points = [('Q',)] + [('H', s) for s in self.S]
        self.new_lines = [('M',)] + [('K', s) for s in self.S]


# ------------------------------------------------------------------ build 1: the construction steps

def by_rules(fr):
    F, q, a, S, T = fr.F, fr.q, fr.a, fr.S, fr.T
    inc = {(p, L) for p in fr.points for L in fr.lines if dot(F, p[1], L[1]) == 0}   # PG(2,q)
    # Step 1: remove (X_s, lam_s): s = a only (AL), all s in S (4hat); then the rotation X_t on lam_sigma(t)
    removed = S if fr.four else (a,)
    for s in removed:
        inc.remove((fr.X(s), fr.lam(s)))
    if fr.four:
        for t in T:
            inc.add((fr.X(t), fr.lam(fr.sigma[t])))
    # Step 2: H_s on every line [w:1:-s], w in F   (= the plane lines through X_s other than ell)
    # Step 3: K_s through every point (x:s:1), x in F (= the plane points of lam_s other than A)
    for s in S:
        for w in fr.els:
            inc.add((('H', s), fr.ln((w, 1, F.neg(s)))))
            inc.add((fr.pt((w, s, 1)), ('K', s)))
    # Step 4: M through P, X_t (t not in T) and all H_s.   Step 5: Q on lam_inf, lam_t (t not in T), all K_s.
    inc.add((fr.P, ('M',)))
    inc.add((('Q',), fr.lam_inf))
    for t in fr.els:
        if t not in T:
            inc.add((fr.X(t), ('M',)))
            inc.add((('Q',), fr.lam(t)))
    for s in S:
        inc.add((('H', s), ('M',)))
        inc.add((('Q',), ('K', s)))
    # Step 6: links
    inc.add((fr.A, ('K', a)))
    inc.add((('H', a), fr.ell))
    if fr.four:
        for t in T:
            inc.add((('H', t), ('K', fr.sigma[t])))
    else:
        inc.add((('H', 0), ('K', 1)))
        inc.add((('H', 1), ('K', 0)))
    return inc


# ------------------------------------------------------------------ build 2: neighbour set of every point

def point_neighbours(fr):
    F, q, a, S, T, E = fr.F, fr.q, fr.a, fr.S, fr.T, fr.els
    neg, mul, add = F.neg, F.mul, F.add
    ln = fr.ln
    N = {}
    N[fr.A] = [fr.lam(t) for t in E] + [fr.lam_inf, ('K', a)]
    N[fr.P] = [fr.ell, fr.lam_inf] + [ln((1, 0, w)) for w in E if w] + [('M',)]
    for t in E:
        through = [ln((w, 1, neg(t))) for w in E if w]          # lines through X_t other than ell, lam_t
        if t not in S:
            N[fr.X(t)] = [fr.ell, fr.lam(t)] + through + [('M',)]
        elif t == a:
            N[fr.X(t)] = [fr.ell] + through + [('M',), ('K', a)] + ([] if fr.four else [])
        elif fr.four:                                            # t in T = {0,1,c}
            N[fr.X(t)] = [fr.ell] + through + [fr.lam(fr.sigma[t]), ('K', t)]
        else:                                                    # AL, t in {0,1}
            N[fr.X(t)] = [fr.ell, fr.lam(t)] + through + [('K', t)]
    for x in E:
        if not x:
            continue
        for y in E:
            N[fr.pt((x, y, 1))] = ([ln((u, 1, neg(add(mul(u, x), y)))) for u in E] + [ln((1, 0, neg(x)))]
                                   + ([('K', y)] if y in S else []))
        N[fr.pt((x, 1, 0))] = [fr.lam_inf] + [ln((1, neg(x), w)) for w in E]
    N[('Q',)] = [fr.lam_inf] + [fr.lam(t) for t in E if t not in T] + [('K', s) for s in S]
    for s in S:
        link = fr.ell if s == a else (('K', fr.sigma[s]) if fr.four else ('K', 1 - s))
        N[('H', s)] = [ln((w, 1, neg(s))) for w in E] + [('M',), link]
    return N


def by_point_table(fr):
    N = point_neighbours(fr)
    inc = {(p, L) for p, Ls in N.items() for L in Ls}
    assert sum(len(Ls) for Ls in N.values()) == len(inc), 'repeated neighbour in point table'
    assert set(N) == set(fr.points) | set(fr.new_points)
    return inc


# ------------------------------------------------------------------ build 3: neighbour set of every line

def line_neighbours(fr):
    F, q, a, S, T, E = fr.F, fr.q, fr.a, fr.S, fr.T, fr.els
    neg, mul, sub, inv = F.neg, F.mul, F.sub, F.inv
    pt = fr.pt
    N = {}
    N[fr.ell] = [fr.P] + [fr.X(t) for t in E] + [('H', a)]
    N[fr.lam_inf] = [fr.A] + [pt((x, 1, 0)) for x in E] + [('Q',)]
    for t in E:
        rest = [pt((x, t, 1)) for x in E if x]                   # points of lam_t other than A, X_t
        if t not in S:
            N[fr.lam(t)] = [fr.A, fr.X(t)] + rest + [('Q',)]
        elif t == a:
            N[fr.lam(t)] = [fr.A] + rest + [('Q',), ('H', a)]
        elif fr.four:
            N[fr.lam(t)] = [fr.A] + rest + [fr.X(fr.sigma_inv[t]), ('H', t)]
        else:
            N[fr.lam(t)] = [fr.A, fr.X(t)] + rest + [('H', t)]
    for u in E:
        if not u:
            continue
        for w in E:
            r = neg(w)                                           # [u:1:w] meets ell in X_{-w}
            N[fr.ln((u, 1, w))] = ([pt((x, sub(neg(mul(u, x)), w), 1)) for x in E] + [pt((neg(inv(u)), 1, 0))]
                                   + ([('H', r)] if r in S else []))
    for w in E:
        if w:
            N[fr.ln((1, 0, w))] = [pt((neg(w), y, 1)) for y in E] + [fr.P]
    N[('M',)] = [fr.P] + [fr.X(t) for t in E if t not in T] + [('H', s) for s in S]
    for s in S:
        link = fr.A if s == a else (('H', fr.sigma_inv[s]) if fr.four else ('H', 1 - s))
        N[('K', s)] = [pt((x, s, 1)) for x in E] + [('Q',), link]
    return N


def by_line_table(fr):
    N = line_neighbours(fr)
    inc = {(p, L) for L, ps in N.items() for p in ps}
    assert sum(len(ps) for ps in N.values()) == len(inc), 'repeated neighbour in line table'
    assert set(N) == set(fr.lines) | set(fr.new_lines)
    return inc


# ------------------------------------------------------------------ filler matching

def delta_point(fr, p):
    x, y, z = p[1]
    return fr.ln((x, z, fr.F.neg(y)))


def filler(fr, inc, d):
    """Join every point p of degree d-1 to delta(p) = [x:z:-y].  Asserts this is a matching of
    non-incident pairs that covers every vertex of degree d-1 (so the result is d-regular)."""
    deg = {}
    for p, L in inc:
        deg[p] = deg.get(p, 0) + 1
        deg[L] = deg.get(L, 0) + 1
    low_p = [p for p in fr.points + fr.new_points if deg[p] < d]
    low_l = {L for L in fr.lines + fr.new_lines if deg[L] < d}
    extra = {(p, delta_point(fr, p)) for p in low_p}
    assert all(deg[p] == d - 1 for p in low_p) and all(deg[L] == d - 1 for L in low_l)
    assert {L for _, L in extra} == low_l and len(extra) == len(low_l), 'delta is not a perfect matching'
    assert not (extra & inc), 'filler pair already incident'
    return inc | extra


def al_paper_matching(fr, inc, all_i=False):
    """AL's printed matching: (P_i, L_i), i in F minus {0,1,a}, and ((x,y),[x,y]) when both have degree q+1.
    P_i = (1:i:0), L_i = [1:0:-i];  (x,y) = (x:y:1), [x,y] = line y = xX + y = [x:-1:y]."""
    F, q = fr.F, fr.q
    deg = {}
    for p, L in inc:
        deg[p] = deg.get(p, 0) + 1
        deg[L] = deg.get(L, 0) + 1
    out = set(inc)
    idx = [i for i in fr.els if i not in ((0,) if all_i else (0, 1, fr.a))]
    pairs = [(fr.pt((1, i, 0)), fr.ln((1, 0, F.neg(i)))) for i in idx]
    pairs += [(fr.pt((x, y, 1)), fr.ln((x, F.neg(1), y))) for x in fr.els for y in fr.els]
    for p, L in pairs:
        if deg[p] == q + 1 and deg[L] == q + 1:
            assert (p, L) not in inc
            out.add((p, L))
    return out


# ------------------------------------------------------------------ graph + checks

def to_graph(fr, inc):
    names = fr.points + fr.new_points + fr.lines + fr.new_lines
    ids = {v: i for i, v in enumerate(names)}
    edges = sorted((ids[p], ids[L]) for p, L in inc)
    return len(names), edges, names


def check(fr, inc, d, D=3):
    """Max degree <= d, every two points collinear, every two lines concurrent, exact diameter (bitset BFS)."""
    n, edges, names = to_graph(fr, inc)
    npts = len(fr.points) + len(fr.new_points)
    adj = [0] * n
    deg = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
        deg[u] += 1
        deg[v] += 1
    # covering properties
    two = [0] * n
    for v in range(n):
        b, acc = adj[v], 0
        while b:
            low = b & -b
            acc |= adj[low.bit_length() - 1]
            b ^= low
        two[v] = acc | (1 << v)
    pmask = (1 << npts) - 1
    lmask = ((1 << n) - 1) ^ pmask
    points_ok = all(two[v] & pmask == pmask for v in range(npts))
    lines_ok = all(two[v] & lmask == lmask for v in range(npts, n))
    # exact diameter
    full = (1 << n) - 1
    diam = 0
    for v in range(n):
        ball, frontier, r = 1 << v, 1 << v, 0
        while ball != full:
            nxt, b = 0, frontier
            while b:
                low = b & -b
                nxt |= adj[low.bit_length() - 1]
                b ^= low
            frontier = nxt & ~ball
            if not frontier:
                return dict(n=n, maxdeg=max(deg), mindeg=min(deg), points_ok=points_ok, lines_ok=lines_ok,
                            diam=None)
            ball |= nxt
            r += 1
        diam = max(diam, r)
    return dict(n=n, maxdeg=max(deg), mindeg=min(deg), points_ok=points_ok, lines_ok=lines_ok, diam=diam,
                edges=len(edges))


def build_all(fr):
    """The three builds; assert they agree; return the core incidence set."""
    r, pt, lt = by_rules(fr), by_point_table(fr), by_line_table(fr)
    assert r == pt, f'rules vs point table differ: {sorted(r ^ pt)[:6]}'
    assert r == lt, f'rules vs line table differ: {sorted(r ^ lt)[:6]}'
    return r


def main():
    qs = [q for q in range(3, 14) if prime_power(q)]
    allok = True
    print('q  | structure | choices | three builds agree | max deg | covering pts/lines | diam core | '
          'filled: regular, diam')
    for q in qs:
        for four in (False, True):
            choices = [(a, c) for a in range(2, q) for c in range(1, q) if c not in (0, 1, a)] if four \
                else [(a, None) for a in range(2, q)]
            if four and q < 4:
                continue
            res = []
            for a, c in choices:
                fr = Frame(q, a, c)
                core = build_all(fr)
                rc = check(fr, core, q + 2)
                full = filler(fr, core, q + 2)
                rf = check(fr, full, q + 2)
                ok = (rc['maxdeg'] == q + 2 and rc['points_ok'] and rc['lines_ok'] and rc['diam'] == 3
                      and rf['maxdeg'] == rf['mindeg'] == q + 2 and rf['diam'] == 3
                      and rc['n'] == 2 * (q * q + q + (6 if four else 5)))
                if four is False:                                   # AL's own printed matching
                    paper = check(fr, al_paper_matching(fr, core), q + 2)
                    allm = check(fr, al_paper_matching(fr, core, all_i=True), q + 2)
                    ok &= allm['mindeg'] == q + 2 and allm['diam'] == 3 and paper['diam'] == 3
                res.append(ok)
                allok &= ok
            tag = '4 hats' if four else 'AL    '
            extra = ''
            if not four:
                extra = f"  [AL paper matching, i not in {{0,1,a}}: min deg {paper['mindeg']}; all i != 0: " \
                        f"min deg {allm['mindeg']}]"
            print(f"{q:2d} | {tag} | {len(choices):3d} | {'yes':3s} | {rc['maxdeg']} | "
                  f"{rc['points_ok']}/{rc['lines_ok']} | {rc['diam']} | {rf['mindeg']}-{rf['maxdeg']}, {rf['diam']}"
                  f" | n={rc['n']} | all {len(res)} choices valid: {all(res)}{extra}")
    print('ALL OK' if allok else 'FAILURES')
    return allok


if __name__ == '__main__':
    sys.exit(0 if main() else 1)
