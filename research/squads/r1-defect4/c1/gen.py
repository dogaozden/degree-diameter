#!/usr/bin/env python3
"""Card c1 of squad r1-defect4: breadth-first normal form seen from point 0, plus lex-leader symmetry breaking.

usage: gen.py k out.cnf

Model. n = k*k-k-1 points (rows) and n lines (columns); X[p][l] = 1 iff point p lies on line l. For k >= 5 the
graph is k-regular (Prop. 3.1 of arXiv:1203.3588), so every row and column of X has exactly k ones. Diameter 3 <=>
any two points share a line and any two lines share a point (both are CNF clauses below).

Step 1: point 0's repeat budget (a proved consequence of the definition).
  Every y != 0 shares >= 1 line with point 0 (diameter 3). Point 0 lies on k lines, each with k-1 other points, so
  sum_{y != 0} (c(0,y) - 1) = k(k-1) - (n-1) = 2, where c(x,y) = number of common lines.
  Hence either (a) one point q has c(0,q) = 3, all others c = 1; or (b) two points q1, q2 have c = 2, others c = 1.
  Relabelling the k lines through point 0 (which is a relabelling of lines, no loss) the pattern of (b) is one of
     b1: q1, q2 both on lines {0,1};  b2: q1 on {0,1}, q2 on {0,2};  b3: q1 on {0,1}, q2 on {2,3}.
  So there are four cases P in {a, b1, b2, b3} (CASES below). A selector s_P per case, at least one true.

Step 2: the fixed block (a relabelling, no loss, for the case P that holds).
  Relabel lines so that the lines through 0 are lines 0..k-1 and the special points sit on the lines named in P.
  Every point y != 0 is on some line < k (it shares a line with 0), and the pattern of y = set of lines < k through y.
  Every non-special point has pattern {j} for one j. Relabel points 1..n-1 in blocks ("classes"): one class per
  pattern, classes listed in the order of CASES[P] followed by the pure classes {0}, {1}, ..., {k-1}. This is a
  relabelling because the classes are disjoint and their sizes are forced by counting: line j < k contains point 0
  and k-1 other points, so the pure class {j} has size (k-1) - (sum of multiplicities of special classes on j).
  Consequence: the first k columns of X (lines 0..k-1) are completely fixed by P. Enforced by unit clauses under s_P.

Step 3: lex-leader (sound symmetry breaking). Let G be the group of relabellings (sigma on points, tau on lines)
that keep the normal form of Step 2: sigma permutes points inside each class (a class has identical fixed columns, so
any permutation inside it keeps the fixed block); tau permutes lines >= k arbitrarily (they are not in the fixed
block); tau restricted to lines < k is a pattern automorphism pi (maps classes onto classes of the same size, sigma
maps each class onto its image in order). Let F be the free block X[1..n-1][k..n-1] in row-major order. For a graph
in normal form, the lex-smallest F over the G-orbit, call it M, satisfies M <=_lex g(M) for every g in G (g(M) is
again in normal form, and the fixed blocks agree, so the comparison is decided by F). We impose M <=_lex g(M) only for
generators g of G:
  - swap of two adjacent points inside a class,
  - swap of two adjacent free lines (k <= c, c+1 < n),
  - transposition (i j) of two lines < k when it is a pattern automorphism.
Each such constraint is implied by lex-minimality, so the formula stays satisfiable iff a graph exists.
Also sound: one selector true per case is enough (point 0 has exactly one pattern), at-most-one is added as a hint.
"""
import sys, itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType

# Case P: list of (lines through point 0, multiplicity) for the special points (see Step 1).
CASES = {
    'a':  [((0, 1, 2), 1)],
    'b1': [((0, 1), 2)],
    'b2': [((0, 1), 1), ((0, 2), 1)],
    'b3': [((0, 1), 1), ((2, 3), 1)],
}


def classes_for(k, spec):
    """Return (n, classes) with classes = [(pattern frozenset, first label, size)] covering labels 1..n-1."""
    n = k * k - k - 1
    cnt = [k - 1] * k
    for P, m in spec:
        for j in P:
            cnt[j] -= m
    assert min(cnt) >= 0
    cls = [(frozenset(P), m) for P, m in spec] + [(frozenset([j]), cnt[j]) for j in range(k) if cnt[j] > 0]
    assert sum(m for _, m in cls) == n - 1
    out, lab = [], 1
    for P, m in cls:
        out.append((P, lab, m))
        lab += m
    return n, out


def pattern_list(k, n, classes):
    pat = [frozenset(range(k))] + [None] * (n - 1)
    for P, start, size in classes:
        for t in range(size):
            pat[start + t] = P
    assert all(p is not None for p in pat)
    return pat


def class_map(classes, pi, n):
    """Point permutation sigma (list over labels) induced by a line permutation pi of lines < k, or None."""
    by_pattern = {P: (start, size) for P, start, size in classes}
    sig = list(range(n))
    for P, start, size in classes:
        Q = frozenset(pi.get(j, j) for j in P)
        if Q not in by_pattern or by_pattern[Q][1] != size:
            return None
        s2 = by_pattern[Q][0]
        for t in range(size):
            sig[start + t] = s2 + t
    return sig


def inverse(perm):
    inv = [0] * len(perm)
    for i, v in enumerate(perm):
        inv[v] = i
    return inv


def build(k):
    n = k * k - k - 1
    pool = IDPool()
    cnf = CNF()
    X = {(p, l): pool.id(('x', p, l)) for p in range(n) for l in range(n)}
    sel = {P: pool.id(('sel', P)) for P in CASES}
    lexctr = itertools.count()

    # Graph constraints (hold for every case): k ones per row and per column (k-regular, Prop. 3.1 of 1203.3588).
    for p in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for l in range(n)], bound=k, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    for l in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for p in range(n)], bound=k, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    # Diameter 3: any two points share a line (side 0), any two lines share a point (side 1).
    for side in (0, 1):
        E = (lambda u, w: X[u, w]) if side == 0 else (lambda u, w: X[w, u])
        for u, v in itertools.combinations(range(n), 2):
            ys = []
            for w in range(n):
                y = pool.id(('y', side, u, v, w))
                cnf.append([-y, E(u, w)])
                cnf.append([-y, E(v, w)])
                ys.append(y)
            cnf.append(ys)

    # Step 1 selectors: at least one pattern (a proved dichotomy), at most one as a hint.
    cnf.append(list(sel.values()))
    for P, Q in itertools.combinations(CASES, 2):
        cnf.append([-sel[P], -sel[Q]])

    def lex_leq(pairs, guard):
        """Add clauses (all guarded by -guard) for xs <=_lex ys, where pairs = [(x_lit, y_lit)] in row-major order.
        Positions with identical literals are always equal and are dropped (they do not change the comparison)."""
        pairs = [(x, y) for x, y in pairs if x != y]
        prev = None
        for idx, (x, y) in enumerate(pairs):
            pre = [-guard] + ([-prev] if prev is not None else [])
            cnf.append(pre + [-x, y])                       # prefix equal  =>  x <= y at this position
            if idx == len(pairs) - 1:
                break
            e = pool.id(('lex', next(lexctr)))              # e: prefix equal up to and including this position
            cnf.append(pre + [-x, -y, e])
            cnf.append(pre + [x, y, e])
            prev = e

    for P, spec in CASES.items():
        g = sel[P]
        n_, classes = classes_for(k, spec)
        assert n_ == n
        pat = pattern_list(k, n, classes)
        # Fixed block: row p has exactly the lines (< k) listed in its pattern. Row 0 is on lines 0..k-1.
        for p in range(n):
            for j in range(k):
                cnf.append([-g, X[p, j] if j in pat[p] else -X[p, j]])
            for j in range(k, n):
                if p == 0:
                    cnf.append([-g, -X[p, j]])   # point 0 is on no line >= k
        rows = range(1, n)          # free rows: points 1..n-1
        cols = range(k, n)          # free columns: lines k..n-1

        def gen_pairs(sig, tau_inv):
            """Pairs (M[r][c], (g M)[r][c]) with (g M)[s][t] = M[sig^-1(s)][tau^-1(t)], row-major over free block."""
            sinv = inverse(sig)
            return [(X[r, c], X[sinv[r], tau_inv[c]]) for r in rows for c in cols]

        ident_c = list(range(n))
        # (i) adjacent points inside a class (any permutation inside a class is a symmetry of the fixed block)
        for P, start, size in classes:
            for t in range(size - 1):
                r = start + t
                sig = list(range(n))
                sig[r], sig[r + 1] = r + 1, r
                lex_leq(gen_pairs(sig, ident_c), g)
        # (ii) adjacent free lines (not in the fixed block, so any permutation of them is a symmetry)
        for c in range(k, n - 1):
            tau_inv = list(range(n))
            tau_inv[c], tau_inv[c + 1] = c + 1, c
            lex_leq(gen_pairs(list(range(n)), tau_inv), g)
        # (iii) transpositions of two lines < k that are pattern automorphisms of this case
        for i, j in itertools.combinations(range(k), 2):
            pi = {i: j, j: i}
            sig = class_map(classes, pi, n)
            if sig is None:
                continue
            lex_leq(gen_pairs(sig, ident_c), g)

    # Output of the encoding: X variables, so that a model can be decoded by the caller.
    return cnf, X, pool


if __name__ == '__main__':
    k = int(sys.argv[1])
    cnf, X, pool = build(k)
    cnf.to_file(sys.argv[2])
    print(f'k={k} n={k*k-k-1} vars={cnf.nv} clauses={len(cnf.clauses)}')
