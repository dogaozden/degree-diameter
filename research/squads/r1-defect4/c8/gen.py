#!/usr/bin/env python3
"""Card c8: baseline CNF for a bipartite (k,3,-4)-graph (research/projects/optimal-sat/defect4/enc_d3m4.py)
plus clauses implied by the repeat identity (every point/line has repeat budget exactly 2).

usage: gen.py k out.cnf
env DEFECT4_RULES = base | exact | all   (ablation switch; default all)

Setting: n = k^2-k-1 points, n lines, every point on k lines, every line has k points (k >= 5, Prop 3.1 of
arXiv:1203.3588); diameter 3 <=> any two points share a line and any two lines share a point.
Normal form (as baseline): point 0 on lines 0..k-1, line 0 through points 0..k-1.

Notation: c(a,b) = #lines through both points a != b (>= 1); m(l,l') = #points on both lines (>= 1).
Auxiliary literals are EXACT functions of X: s(a,b) <=> c(a,b)>=2, q(a,b) <=> c(a,b)>=3, t(l,l') <=> m>=2,
u(l,l') <=> m>=3 (built with a full sequential counter, both directions).
"""
import sys, os, itertools
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType


def build(k, rules='all'):
    n = k * k - k - 1
    pool = IDPool()
    cnf = CNF()
    T = pool.id(('T',))          # constant true (unit clause); its negation is constant false
    cnf.append([T])

    def add(cl):                 # add a clause, dropping constant-false literals, skipping satisfied ones
        out = []
        for l in cl:
            if l == T:
                return
            if l == -T:
                continue
            out.append(l)
        cnf.append(out)

    X = {(p, l): pool.id(('x', p, l)) for p in range(n) for l in range(n)}

    # ---- baseline (identical to enc_d3m4.py) ----
    for l in range(n):
        cnf.append([X[0, l]] if l < k else [-X[0, l]])
    for p in range(1, n):
        cnf.append([X[p, 0]] if p < k else [-X[p, 0]])
    for p in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for l in range(n)], bound=k, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    for l in range(n):
        cnf.extend(CardEnc.equals([X[p, l] for p in range(n)], bound=k, vpool=pool,
                                  encoding=EncType.seqcounter).clauses)
    for side in (0, 1):
        E = (lambda u, w: X[u, w]) if side == 0 else (lambda u, w: X[w, u])
        for u, v in itertools.combinations(range(n), 2):
            ys = []
            for w in range(n):
                y = pool.id(('y', side, u, v, w))
                cnf.append([-y, E(u, w)]); cnf.append([-y, E(v, w)])
                ys.append(y)
            cnf.append(ys)
    if rules == 'base':
        return cnf, n

    cid = [0]

    def exact_counter(lits, K):
        """Returns [T, o_1, ..., o_K] with o_j <=> (sum(lits) >= j)  (full equivalence)."""
        prev = [T] + [-T] * K
        for x in lits:
            cur = [T]
            for j in range(1, K + 1):
                A, B = prev[j], prev[j - 1]
                cid[0] += 1
                c = pool.id(('cnt', cid[0]))
                # c <=> A or (B and x)
                add([-A, c]); add([-B, -x, c]); add([-c, A, B]); add([-c, A, x])
                cur.append(c)
            prev = cur
        return prev

    # Point pairs: z <=> x_p,l & x_q,l ; cnt[(p,q)][j] <=> c(p,q) >= j, j = 1..3
    pcnt = {}
    for p, q in itertools.combinations(range(n), 2):
        zs = []
        for l in range(n):
            z = pool.id(('zp', p, q, l))
            add([-z, X[p, l]]); add([-z, X[q, l]]); add([z, -X[p, l], -X[q, l]])
            zs.append(z)
        pcnt[(p, q)] = exact_counter(zs, 3)

    def cge(p, q, j):           # literal for c(p,q) >= j
        return pcnt[(min(p, q), max(p, q))][j]

    # Line pairs: z <=> X[p,l] & X[p,l'] over points p ; lcnt[(l,l')][j] <=> m(l,l') >= j
    lcnt = {}
    for l, l2 in itertools.combinations(range(n), 2):
        zs = []
        for p in range(n):
            z = pool.id(('zl', l, l2, p))
            add([-z, X[p, l]]); add([-z, X[p, l2]]); add([z, -X[p, l], -X[p, l2]])
            zs.append(z)
        lcnt[(l, l2)] = exact_counter(zs, 3)

    def mge(l, l2, j):          # literal for m(l,l') >= j
        return lcnt[(min(l, l2), max(l, l2))][j]

    # ---- RULE 0: exact repeat budget ----
    # Proof: for a point a, double count (L, b) with a,b in L: sum_{b != a} c(a,b) = sum_{L ∋ a} (k-1) = k(k-1).
    # There are n-1 = k^2-k-2 other points and c >= 1 for all of them (baseline), so
    # sum_{b != a} (c(a,b)-1) = 2. Each term is 0,1,2 so c <= 3 and c-1 = [c>=2] + [c>=3].
    # Hence exactly 2 of the literals {s(a,b), q(a,b) : b != a} are true. The same argument on the dual
    # (k points per line, every two lines meet, every two points share a line) gives the line version.
    if rules in ('exact', 'all'):
        for a in range(n):
            lits = []
            for b in range(n):
                if b != a:
                    lits += [cge(a, b, 2), cge(a, b, 3)]
            cnf.extend(CardEnc.equals(lits, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses)
        for l in range(n):
            lits = []
            for l2 in range(n):
                if l2 != l:
                    lits += [mge(l, l2, 2), mge(l, l2, 3)]
            cnf.extend(CardEnc.equals(lits, bound=2, vpool=pool, encoding=EncType.seqcounter).clauses)

    if rules != 'all':
        return cnf, n

    # ---- RULE A: forced repeat across a pair of lines sharing two points ----
    # Let l != l' with m = |l ∩ l'| >= 2, a in l, I = l' \ {a}, S = sum_{b in I} (c(a,b)-1).
    # Double count (L,b), L ∋ a, b ∈ L ∩ I: sum_{b in I} c(a,b) = sum_{L ∋ a} |L ∩ I|.
    # If a not in l': |I| = k and the k lines through a give k + S = m + sum_{L∋a, L≠l} |L ∩ l'|, and every
    # such L meets l' (two lines share a point), so S = m-1+E with E >= 0.
    # If a in l': |I| = k-1; lines through a give (m-1) + (k-1) + sum_{others}(|L∩l'|-1), so again S = m-1+E.
    # Either way S >= m-1 >= 1: some point b on l', b != a, has c(a,b) >= 2.
    # Clause: not t(l,l') or not X[a,l] or OR_{b != a} w(a,b,l'), with w => s(a,b) and w => X[b,l'].
    if rules == 'all':
        wpt = {}

        def w_pt(a, b, l2):
            key = (a, b, l2)
            if key not in wpt:
                w = pool.id(('wpt', a, b, l2))
                add([-w, cge(a, b, 2)]); add([-w, X[b, l2]])
                wpt[key] = w
            return wpt[key]

        for l, l2 in itertools.permutations(range(n), 2):
            t = mge(l, l2, 2)
            for a in range(n):
                add([-t, -X[a, l]] + [w_pt(a, b, l2) for b in range(n) if b != a])

        # ---- RULE A* (dual of RULE A): points p != q with c(p,q) >= 2 ----
        # Same proof with points and lines exchanged (the hypotheses used are self-dual): every line L ∋ p has
        # a line L' != L through q with |L ∩ L'| >= 2.
        # Clause: not s(p,q) or not X[p,L] or OR_{L' != L} w'(L,L',q), with w' => t(L,L') and w' => X[q,L'].
        wln = {}

        def w_ln(l, l2, q):
            key = (l, l2, q)
            if key not in wln:
                w = pool.id(('wln', l, l2, q))
                add([-w, mge(l, l2, 2)]); add([-w, X[q, l2]])
                wln[key] = w
            return wln[key]

        for p, q in itertools.permutations(range(n), 2):
            s = cge(p, q, 2)
            for l in range(n):
                add([-s, -X[p, l]] + [w_ln(l, l2, q) for l2 in range(n) if l2 != l])

    return cnf, n


if __name__ == '__main__':
    k = int(sys.argv[1])
    rules = os.environ.get('DEFECT4_RULES', 'all')
    cnf, n = build(k, rules)
    cnf.to_file(sys.argv[2])
    print(f'k={k} n={n} rules={rules} vars={cnf.nv} clauses={len(cnf.clauses)}')
