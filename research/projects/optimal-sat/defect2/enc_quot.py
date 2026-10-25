#!/usr/bin/env python3
"""CNF for the quotient form of a bipartite (k,3,-2)-graph (../SUMMARY.md, Theorem Q).

A (k,3,-2)-graph exists iff there is an oriented graph A on m = k(k-1)/2 vertices with
  (1) every vertex has out-degree and in-degree k-2;
  (2) adjacent vertices (either direction) have no common out-neighbour and no common in-neighbour;
  (3) non-adjacent vertices have exactly 2 common out-neighbours and exactly 2 common in-neighbours;
(equivalently M = 2I + A satisfies M M^T = M^T M = kI + 2J), and a signing s of the arcs such that W = signed A is a
weighing matrix, W W^T = (k-2) I; given (1)-(3) this says: for non-adjacent c,d with common out-neighbours e1,e2,
s(c,e1)+s(d,e1)+s(c,e2)+s(d,e2) is odd.

Normal form: vertex 0 has out-neighbours 1..k-2 and in-neighbours k-1..2k-4 (always possible by relabelling).
--sym adds lex-leader clauses for adjacent transpositions inside O={1..k-2}, I={k-1..2k-4}, R={2k-3..m-1}
(row-major order of the a-variables); --signs adds the weighing-matrix signing with a gauge fix.
usage: enc_quot.py k out.cnf [--signs] [--sym] [--insigns] [--nf2]
--alltr: with --nf2 --sym, lex-leader for all transpositions of O and of I (not only adjacent ones).
--ntt: add 'no transitive triangle' clauses (implied by Lemma Q2 at every vertex).
--nf2: second normal form (Lemma Q2): R labelled by the pairs of O, all arcs between R and O fixed.
"""
import sys, itertools, json
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType

def build(k, signs=False, sym=False, insigns=False, nf2=False, ntt=False, alltr=False, pb=None):
    """pb: if a list is given, cardinality and pair conditions are appended to it as linear constraints
    (list of (terms, op, rhs), terms = [(coef, var)]) instead of being encoded as CNF."""
    m = k * (k - 1) // 2
    g = k - 2
    pool = IDPool()
    cnf = CNF()
    V = range(m)
    a = {(c, d): pool.id(('a', c, d)) for c in V for d in V if c != d}
    O = list(range(1, g + 1)); I = list(range(g + 1, 2 * g + 1)); R = list(range(2 * g + 1, m))
    # normal form at vertex 0
    for d in V:
        if d == 0: continue
        cnf.append([a[0, d]] if d in O else [-a[0, d]])
        cnf.append([a[d, 0]] if d in I else [-a[d, 0]])
    for c, d in itertools.combinations(V, 2):
        cnf.append([-a[c, d], -a[d, c]])
    if ntt:
        # Lemma Q2 at every vertex = no transitive triangle (a->b, a->c, b->c); implied, added for propagation.
        for p, q, r in itertools.permutations(V, 3):
            cnf.append([-a[p, q], -a[p, r], -a[q, r]])
    if nf2:
        # Lemma Q2: O and I are independent, no arcs I->O, and y -> O cap O_y is a bijection R -> pairs of O.
        # Label R = pairs (i,j) of O in lexicographic order; y_(i,j) -> x_i, x_j and no other arcs R -> O.
        pairs = list(itertools.combinations(O, 2))
        assert len(pairs) == len(R)
        for y, (i, j) in zip(R, pairs):
            for x in O:
                cnf.append([a[y, x]] if x in (i, j) else [-a[y, x]])
        for x, x2 in itertools.permutations(O, 2): cnf.append([-a[x, x2]])
        for z, z2 in itertools.permutations(I, 2): cnf.append([-a[z, z2]])
        for z in I:
            for x in O: cnf.append([-a[z, x]])
    for c in V:
        if pb is not None:
            pb.append(([(1, a[c, d]) for d in V if d != c], '=', g))
            pb.append(([(1, a[d, c]) for d in V if d != c], '=', g))
            continue
        cnf.extend(CardEnc.equals([a[c, d] for d in V if d != c], bound=g, vpool=pool, encoding=EncType.seqcounter).clauses)
        cnf.extend(CardEnc.equals([a[d, c] for d in V if d != c], bound=g, vpool=pool, encoding=EncType.seqcounter).clauses)
    def counter(ys):
        prev = [None, None, None]
        for y in ys:
            cur = []
            for j in range(3):
                s = pool.id(); A_ = prev[j]; B_ = prev[j - 1] if j > 0 else 'T'
                if A_ is not None: cnf.append([-A_, s])
                if B_ == 'T': cnf.append([-y, s])
                elif B_ is not None: cnf.append([-B_, -y, s])
                cnf.append([-s, y] + ([A_] if A_ is not None else []))
                if B_ != 'T': cnf.append([-s] + ([A_] if A_ is not None else []) + ([B_] if B_ is not None else []))
                cur.append(s)
            prev = cur
        return prev
    Y = {}
    for c, d in itertools.combinations(V, 2):
        adj = pool.id(('adj', c, d))
        cnf.append([-adj, a[c, d], a[d, c]]); cnf.append([adj, -a[c, d]]); cnf.append([adj, -a[d, c]])
        for direction in ('out', 'in'):
            ys = []
            for e in V:
                if e in (c, d): continue
                y = pool.id(('y', direction, c, d, e))
                u, v = (a[c, e], a[d, e]) if direction == 'out' else (a[e, c], a[e, d])
                cnf.append([-y, u]); cnf.append([-y, v]); cnf.append([y, -u, -v])
                ys.append(y); Y[direction, c, d, e] = y
            if pb is not None:
                # 2(a_cd + a_dc) + sum_e y_e = 2  (off-diagonal entry of (2I+A)(2I+A)^T resp. (2I+A)^T(2I+A))
                pb.append(([(2, a[c, d]), (2, a[d, c])] + [(1, y) for y in ys], '=', 2))
                continue
            s1, s2, s3 = counter(ys)
            cnf.append([-s3])
            cnf.append([-adj, -s1])        # adjacent: none
            cnf.append([adj, s2])          # non-adjacent: exactly two
    if signs:
        s = {(c, d): pool.id(('s', c, d)) for c in V for d in V if c != d}
        def xor_def(z, p, q):
            cnf.append([-z, p, q]); cnf.append([-z, -p, -q]); cnf.append([z, -p, q]); cnf.append([z, p, -q])
        dirs = ('out', 'in') if insigns else ('out',)
        for direction in dirs:
            for c, d in itertools.combinations(V, 2):
                zs = {}
                for e in V:
                    if e in (c, d): continue
                    z = pool.id(('z', direction, c, d, e))
                    if direction == 'out': xor_def(z, s[c, e], s[d, e])
                    else: xor_def(z, s[e, c], s[e, d])
                    zs[e] = z
                es = [e for e in V if e not in (c, d)]
                for e1, e2 in itertools.combinations(es, 2):
                    y1, y2 = Y[direction, c, d, e1], Y[direction, c, d, e2]
                    cnf.append([-y1, -y2, zs[e1], zs[e2]]); cnf.append([-y1, -y2, -zs[e1], -zs[e2]])
        # gauge: columns in O via arcs (0,x); rows in I via arcs (z,0); rows in R via first arc into O;
        # columns in R via first arc from I.  These fixed arcs form a forest, so any solution can be gauged to them.
        for x in O: cnf.append([-s[0, x]])
        for z in I: cnf.append([-s[z, 0]])
        for y in R:
            for i, x in enumerate(O):
                cnf.append([-a[y, x]] + [a[y, x2] for x2 in O[:i]] + [-s[y, x]])
            for i, z in enumerate(I):
                cnf.append([-a[z, y]] + [a[z2, y] for z2 in I[:i]] + [-s[z, y]])
    if sym:
        order = [(c, d) for c in V for d in V if c != d]
        def lexleader(pi):
            seq = []
            for (c, d) in order:
                c2, d2 = pi(c), pi(d)
                if (c2, d2) != (c, d): seq.append((a[c, d], a[c2, d2]))
            e = None
            for i, (x, y) in enumerate(seq):
                cnf.append(([-e] if e else []) + [-x, y])
                if i == len(seq) - 1: break
                e2 = pool.id()
                cnf.append(([-e] if e else []) + [-x, -y, e2]); cnf.append(([-e] if e else []) + [x, y, e2]); e = e2
        if nf2:
            pairs = list(itertools.combinations(O, 2))
            pidx = {p: y for y, p in zip(R, pairs)}
            Opairs_ = list(itertools.combinations(O, 2)) if alltr else [(O[i], O[i + 1]) for i in range(len(O) - 1)]
            Ipairs_ = list(itertools.combinations(I, 2)) if alltr else [(I[i], I[i + 1]) for i in range(len(I) - 1)]
            for (u, v) in Opairs_:
                sw = lambda t, u=u, v=v: v if t == u else (u if t == v else t)
                def pi(t, sw=sw):
                    if t in pidx.values():
                        p = pairs[R.index(t)]
                        q = tuple(sorted((sw(p[0]), sw(p[1]))))
                        return pidx[q]
                    return sw(t)
                lexleader(pi)
            for (u, v) in Ipairs_:
                lexleader(lambda t, u=u, v=v: v if t == u else (u if t == v else t))
        else:
            for blk in (O, I, R):
                for i in range(len(blk) - 1):
                    u, v = blk[i], blk[i + 1]
                    lexleader(lambda t, u=u, v=v: v if t == u else (u if t == v else t))
    return cnf, pool, a

if __name__ == '__main__':
    k = int(sys.argv[1])
    cnf, pool, a = build(k, signs='--signs' in sys.argv, sym='--sym' in sys.argv, insigns='--insigns' in sys.argv,
                         nf2='--nf2' in sys.argv, ntt='--ntt' in sys.argv,
                         alltr='--alltr' in sys.argv)
    cnf.to_file(sys.argv[2])
    with open(sys.argv[2] + '.map', 'w') as f:
        json.dump({'k': k, 'a': [[c, d, v] for (c, d), v in a.items()]}, f)
    print(f'k={k} vars={cnf.nv} clauses={len(cnf.clauses)}')
