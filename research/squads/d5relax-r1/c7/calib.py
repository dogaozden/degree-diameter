#!/usr/bin/env python3
"""Card c7 (squad d5relax-r1): exact SAT test of relaxed sets of W(q) WITHOUT the spread condition.

Relaxed: every point of T has at most one collinear point in T (pairs may lie on any line).
Encoding over x_p (p = 0..n-1, variable p+1):
  - every line: no three of its points in T;
  - every point v, lines L1 != L2 through v, a in L1-v, b in L2-v: not (v and a and b);
  - sum x >= K (pysat CardEnc.atleast).
Cases (PSp(4,q) is transitive on points, on ordered collinear pairs and on ordered non-collinear pairs):
  full : no symmetry (used for validation)
  A    : 0 in T and p1 = 1 in T (a pair); all other neighbours of 0 and 1 are out
  B    : 0 in T, no neighbour of 0 in T, p2 in T for p2 = smallest point not collinear with 0
  check: calib.py Q 0 check FILE : soundness check, fix x to the witness in FILE (size K = |witness|) and solve the full formula.
usage: calib.py Q K CASE [SOLVER] [ENC]     (ENC: totalizer | seqcounter)
"""
import sys, time, json
from itertools import combinations
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType

DD = '/home/user/degree-diameter/research/theorems/d5relax/data'


def load(q):
    rd = open('%s/W%d_lines.txt' % (DD, q)).read().split('\n')
    nl = int(rd[0].split()[0])
    lines = [tuple(map(int, rd[1 + i].split())) for i in range(nl)]
    ad = open('%s/W%d_adj.txt' % (DD, q)).read().split('\n')
    n = int(ad[0].split()[0])
    adj = [set(map(int, ad[1 + i].split()[1:])) for i in range(n)]
    col = [set() for _ in range(n)]
    for l in lines:
        assert len(l) == q + 1
        for a in l:
            for b in l:
                if a != b:
                    col[a].add(b)
    assert col == adj, 'line file and adjacency file disagree'
    assert all(len(c) == q * (q + 1) for c in col)
    return n, lines, col


def clauses_relaxed(n, lines, col):
    cls = []
    for l in lines:                       # no three points of a line
        for a, b, c in combinations(l, 3):
            cls.append([-(a + 1), -(b + 1), -(c + 1)])
    for v in range(n):                    # v with two neighbours on different lines
        lv = [l for l in lines if v in l]
        for L1, L2 in combinations(lv, 2):
            for a in L1:
                if a == v:
                    continue
                for b in L2:
                    if b == v:
                        continue
                    cls.append([-(v + 1), -(a + 1), -(b + 1)])
    return cls


def units_for_case(case, n, col):
    if case == 'full':
        return []
    if case == 'A':
        p1 = min(col[0])
        u = [[1], [p1 + 1]]
        for y in (col[0] | col[p1]) - {0, p1}:
            u.append([-(y + 1)])
        return u
    if case == 'B':
        p2 = min(y for y in range(1, n) if y not in col[0])
        u = [[1], [p2 + 1]]
        for y in col[0]:
            u.append([-(y + 1)])
        return u
    raise SystemExit('bad case ' + case)


def read_set(path):
    s = open(path).read().strip()
    if s.startswith('['):
        return json.loads(s)
    return [int(x) for x in s.split()[1:]]


def main():
    q, K, case = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    sname = sys.argv[4] if (len(sys.argv) > 4 and case != 'check') else 'cadical195'
    enc = EncType.totalizer if (len(sys.argv) <= 5 or sys.argv[5] == 'totalizer') else EncType.seqcounter
    n, lines, col = load(q)
    cls = clauses_relaxed(n, lines, col)
    if case == 'check':
        T = read_set(sys.argv[4])
        K = len(T)
        card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=K, top_id=n, encoding=enc)
        cls2 = cls + card.clauses
        assum = [(p + 1) if p in T else -(p + 1) for p in range(n)]
        with Solver(name=sname, bootstrap_with=cls2) as s:
            ok = s.solve(assumptions=assum)
        print('CHECK q=%d witness size %d: formula %s' % (q, K, 'SATISFIED (encoding accepts it)' if ok else 'VIOLATED'))
        return
    cls += units_for_case(case, n, col)
    card = CardEnc.atleast(lits=list(range(1, n + 1)), bound=K, top_id=n, encoding=enc)
    cls += card.clauses
    t0 = time.time()
    with Solver(name=sname, bootstrap_with=cls) as s:
        ok = s.solve()
        dt = time.time() - t0
        if ok:
            m = s.get_model()
            T = [p for p in range(n) if m[p] > 0]
            for t in T:
                assert sum(1 for u in T if u in col[t]) <= 1
            print('SAT q=%d K=%d case=%s %s %.1fs |T|=%d T=%s' % (q, K, case, sname, dt, len(T), json.dumps(T)))
        else:
            print('UNSAT q=%d K=%d case=%s %s %.1fs' % (q, K, case, sname, dt))


if __name__ == '__main__':
    main()
