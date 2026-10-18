"""Degree q+2, diameter 4 (q odd): P(W(q),x) plus point copies on a weighted 2-ovoid made of two elliptic quadrics.

Points (a, w), w = (b, c) in AG(2,q) (see as_gq.py). N(b, c) = b^2 - eps c^2 with eps a non-square (anisotropic).
Q_k = {(c_k N(w), w) : w in AG(2,q)} for k = 1, 2, with c_1 c_2 = 1/(4 eps). Then every line of P(W(q),x) meets
Q_1 and Q_2 in a total of exactly 2 points, counted with multiplicity (Q_1 and Q_2 share only e = (0,0,0)).
Copy every point of Q_1 and of Q_2 once (so e is copied twice). Each line gains exactly 2 neighbours, so the
graph has maximum degree q+2 and order q^3 + (q+2)q^2 + 2q^2 = 2q^2(q+2).

python3 as_w2.py q [c1]   checks the 2-ovoid, builds the graph, checks it with lib.is_valid, writes
graphs/as_w2_q{q}_n{n}.json.
"""
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from as_gq import build, check_gq, incidence_edges, lib  # noqa: E402


def weighted_2ovoid(F, pts, c1=1):
    q = F.q
    sq = {F.mul(x, x) for x in range(1, q)}
    eps = next(e for e in range(1, q) if e not in sq)
    four = F.add(F.add(1, 1), F.add(1, 1))
    c2 = F.inv(F.mul(F.mul(four, eps), c1))
    idx = {p: i for i, p in enumerate(pts)}
    N = lambda b, c: F.sub(F.mul(b, b), F.mul(eps, F.mul(c, c)))
    W = Counter()
    for ck in (c1, c2):
        for b in range(q):
            for c in range(q):
                W[idx[(F.mul(ck, N(b, c)), b, c)]] += 1
    return W, eps, c2


def main():
    q = int(sys.argv[1])
    c1 = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    F, pts, lines = build(q)
    check_gq(q, pts, lines)
    W, eps, c2 = weighted_2ovoid(F, pts, c1)
    per_line = Counter(sum(W[p] for p in L) for L in lines)
    print(f'q={q} eps={eps} c1={c1} c2={c2}: |W|={sum(W.values())}, weights {dict(Counter(W.values()))}, '
          f'line sums {dict(per_line)}')
    assert per_line == Counter({2: len(lines)}), 'not a weighted 2-ovoid'
    n0 = len(pts)
    N0 = n0 + len(lines)
    edges = incidence_edges(n0, lines)
    on = [[] for _ in range(n0)]
    for j, L in enumerate(lines):
        for p in L:
            on[p].append(n0 + j)
    v = N0
    for p, w in sorted(W.items()):
        for _ in range(w):
            edges += [(v, Lv) for Lv in on[p]]
            v += 1
    n = v
    assert n == 2 * q * q * (q + 2)
    ok = lib.is_valid(n, edges, q + 2, 4)
    print(f'graph: n={n}, max degree {lib.max_degree(n, edges)}, is_valid(deg {q+2}, D 4) = {ok}')
    if ok:
        out = HERE / 'graphs' / f'as_w2_q{q}_n{n}.json'
        out.write_text(json.dumps({'case': f'd{q+2}D4', 'value': n, 'output': [n, [list(e) for e in edges]]}))
        print('wrote', out)


if __name__ == '__main__':
    main()
