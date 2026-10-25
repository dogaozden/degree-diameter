#!/usr/bin/env python3
"""Grid-form CNF for a bipartite (k,3,-2)-graph (see ../SUMMARY.md, Lemma 2).

g = k-2. After fixing one 4-cycle (points 0,1; lines 0,1), the g 4-cycles of lines through 0/1 (rows i, columns j)
and the g 4-cycles of points on lines 0/1 (a_r on line 0, b_r on line 1), all incidences outside the "grid" are forced.
What is left:
  grid points  GP = d(i,a) (i<g, a<2; row i, col i)  and  c(i,j) (i != j; row i, col j)      -- g^2+g points
  grid lines   GL = D(r,b) (r<g, b<2; class r, class' r) and C(r,s) (r != s; class r, class' s) -- g^2+g lines
  x[u][l] = point u on line l.
Constraints:
  T  every grid line has exactly one point in each row and exactly one in each column;
  R  every grid point lies on exactly one line of each r-class and exactly one line of each s-class;
  P  two grid points in different rows and columns share 1 + PP[u][v] lines (PP = pairing of cell points);
  L  two grid lines in different r- and s-classes share 1 + LL[l][m] points (LL = pairing of cell lines);
  M  PP and LL are perfect matchings.
usage: enc_grid.py k out.cnf [--sym]  (writes out.cnf and out.cnf.map with the x-variable numbering)
"""
import sys, itertools, json
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType

def build(k, sym=False, maxlen=10**9):
    g = k - 2
    pool = IDPool()
    cnf = CNF()
    GP = [('d', i, a) for i in range(g) for a in range(2)] + [('c', i, j) for i in range(g) for j in range(g) if i != j]
    GL = [('D', r, b) for r in range(g) for b in range(2)] + [('C', r, s) for r in range(g) for s in range(g) if r != s]
    row = lambda u: u[1]
    col = lambda u: u[1] if u[0] in ('d', 'D') else u[2]
    X = {}
    for u in GP:
        for l in GL:
            X[u, l] = pool.id(('x', u, l))
    def exactly1(lits):
        cnf.append(lits)
        cnf.extend(CardEnc.atmost(lits, bound=1, vpool=pool, encoding=EncType.seqcounter).clauses)
    # T
    for l in GL:
        for i in range(g):
            exactly1([X[u, l] for u in GP if row(u) == i])
            exactly1([X[u, l] for u in GP if col(u) == i])
    # R
    for u in GP:
        for r in range(g):
            exactly1([X[u, l] for l in GL if row(l) == r])
            exactly1([X[u, l] for l in GL if col(l) == r])
    # matchings
    PP = {}
    cells = [u for u in GP if u[0] == 'c']
    for u, v in itertools.combinations(cells, 2):
        if row(u) != row(v) and col(u) != col(v):
            PP[u, v] = PP[v, u] = pool.id(('pp', u, v))
    LL = {}
    clines = [l for l in GL if l[0] == 'C']
    for l, m in itertools.combinations(clines, 2):
        if row(l) != row(m) and col(l) != col(m):
            LL[l, m] = LL[m, l] = pool.id(('ll', l, m))
    for u in cells:
        exactly1([PP[u, v] for v in cells if (u, v) in PP])
    for l in clines:
        exactly1([LL[l, m] for m in clines if (l, m) in LL])
    # counter with full equivalence: returns literals s1,s2,s3 meaning sum>=1,2,3
    def counter(ys):
        prev = [None, None, None]  # s_{i-1}[1..3]; None = false
        for y in ys:
            cur = []
            for j in range(3):
                s = pool.id()
                a = prev[j]          # s_{i-1}[j+1]
                b = prev[j - 1] if j > 0 else 'T'  # s_{i-1}[j]
                # s <-> a or (b and y)
                if a is not None:
                    cnf.append([-a, s])
                if b == 'T':
                    cnf.append([-y, s])
                elif b is not None:
                    cnf.append([-b, -y, s])
                # s -> a or y ; s -> a or b
                cl = [-s, y] + ([a] if a is not None else [])
                cnf.append(cl)
                if b != 'T':
                    cl = [-s] + ([a] if a is not None else []) + ([b] if b is not None else [])
                    cnf.append(cl)
                cur.append(s)
            prev = cur
        return prev
    def common(pairs, sel, pairvar):
        for (u, v) in pairs:
            ys = []
            for w in sel(u, v):
                y = pool.id()
                a, b = w
                cnf.append([-y, a]); cnf.append([-y, b]); cnf.append([y, -a, -b])
                ys.append(y)
            s1, s2, s3 = counter(ys)
            cnf.append([s1]); cnf.append([-s3])
            pv = pairvar(u, v)
            if pv is None:
                cnf.append([-s2])
            else:
                cnf.append([-s2, pv]); cnf.append([s2, -pv])
    # P
    ppairs = [(u, v) for u, v in itertools.combinations(GP, 2) if row(u) != row(v) and col(u) != col(v)]
    common(ppairs, lambda u, v: [(X[u, l], X[v, l]) for l in GL], lambda u, v: PP.get((u, v)))
    # L
    lpairs = [(l, m) for l, m in itertools.combinations(GL, 2) if row(l) != row(m) and col(l) != col(m)]
    common(lpairs, lambda l, m: [(X[u, l], X[u, m]) for u in GP], lambda l, m: LL.get((l, m)))
    if sym:
        add_symbreak(cnf, pool, g, GP, GL, X, maxlen)
    return cnf, pool, GP, GL, X

def add_symbreak(cnf, pool, g, GP, GL, X, maxlen):
    """Lex-leader clauses x <= pi(x) for generators pi of the known symmetry group (line-major order)."""
    order = [(u, l) for l in GL for u in GP]
    def lexleader(pmap):
        seq = [(X[v], X[pmap(v)]) for v in order if pmap(v) != v][:maxlen]
        if not seq:
            return
        e = None  # e = 'equal so far' literal; None means true
        for i, (a, b) in enumerate(seq):
            # e -> (a <= b)
            cnf.append(([-e] if e else []) + [-a, b])
            if i == len(seq) - 1:
                break
            e2 = pool.id()
            cnf.append(([-e] if e else []) + [-a, -b, e2])
            cnf.append(([-e] if e else []) + [a, b, e2])
            e = e2
    def perm_pt(f):
        return lambda v: (f(v[0]), v[1])
    def perm_ln(f):
        return lambda v: (v[0], f(v[1]))
    gens = []
    for i in range(g - 1):  # rows/cols i <-> i+1
        sw = lambda t, i=i: i + 1 if t == i else (i if t == i + 1 else t)
        gens.append(perm_pt(lambda u, sw=sw: (u[0], sw(u[1]), u[2]) if u[0] == 'd' else ('c', sw(u[1]), sw(u[2]))))
        gens.append(perm_ln(lambda l, sw=sw: (l[0], sw(l[1]), l[2]) if l[0] == 'D' else ('C', sw(l[1]), sw(l[2]))))
    for i in range(g):
        gens.append(perm_pt(lambda u, i=i: ('d', i, 1 - u[2]) if (u[0] == 'd' and u[1] == i) else u))
        gens.append(perm_ln(lambda l, i=i: ('D', i, 1 - l[2]) if (l[0] == 'D' and l[1] == i) else l))
    gens.append(perm_pt(lambda u: ('c', u[2], u[1]) if u[0] == 'c' else u))
    gens.append(perm_ln(lambda l: ('C', l[2], l[1]) if l[0] == 'C' else l))
    dual_pt = lambda u: (u[0].upper(), u[1], u[2])
    dual_ln = lambda l: (l[0].lower(), l[1], l[2])
    gens.append(lambda v: (dual_ln(v[1]), dual_pt(v[0])))
    for pm in gens:
        lexleader(pm)

if __name__ == '__main__':
    k = int(sys.argv[1])
    sym = '--sym' in sys.argv
    cnf, pool, GP, GL, X = build(k, sym=sym)
    cnf.to_file(sys.argv[2])
    with open(sys.argv[2] + '.map', 'w') as f:
        json.dump({'k': k, 'x': [[list(u), list(l), v] for (u, l), v in X.items()]}, f)
    print(f'k={k} vars={cnf.nv} clauses={len(cnf.clauses)}')
