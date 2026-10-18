"""Degree q+3, diameter 4 (q odd): P(W(q),x) + copies of the weighted 2-ovoid Q_1 + Q_2 (as_w2.py) + copies of a
partial ovoid O (points, no two on a line) + copies of a spread (the q^2 lines {(a, w) : a}, one per w).

Each old line gains 2 (from Q_1 + Q_2) plus at most 1 (from O): degree <= q+3. Each old point gains 1 (the spread
copy through it): degree q+3. Copies keep their originals' degrees (q+2 and q). Order 2q^3 + 2q^2 + 2q^2 + |O| + q^2.

python3 as_deg3.py q OVOID.txt   (OVOID.txt: point indices of as_gq.build(q), one per line; checked here)
writes graphs/as_deg3_q{q}_n{n}.json if lib.is_valid passes.
"""
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from as_gq import build, check_gq, incidence_edges, lib  # noqa: E402
from as_w2 import weighted_2ovoid  # noqa: E402


def main():
    q = int(sys.argv[1])
    O = [int(x) for x in Path(sys.argv[2]).read_text().split()]
    F, pts, lines = build(q)
    check_gq(q, pts, lines)
    W, eps, c2 = weighted_2ovoid(F, pts)
    Oc = Counter(O)
    assert max(Oc.values()) == 1
    assert all(sum(1 for p in L if p in Oc) <= 1 for L in lines), 'O is not a partial ovoid'
    W.update(Oc)
    sums = Counter(sum(W[p] for p in L) for L in lines)
    print(f'q={q}: |W|={sum(W.values())}, line sums {dict(sums)}')
    n0 = len(pts)
    spread = [j for j, L in enumerate(lines) if len({pts[p][1:] for p in L}) == 1]  # fibres over w
    assert len(spread) == q * q and len({p for j in spread for p in lines[j]}) == n0
    on = [[] for _ in range(n0)]
    for j, L in enumerate(lines):
        for p in L:
            on[p].append(n0 + j)
    edges = incidence_edges(n0, lines)
    v = n0 + len(lines)
    for p, w in sorted(W.items()):
        for _ in range(w):
            edges += [(v, Lv) for Lv in on[p]]
            v += 1
    for j in spread:
        edges += [(p, v) for p in lines[j]]
        v += 1
    n = v
    ok = lib.is_valid(n, edges, q + 3, 4)
    print(f'graph: n={n}, max degree {lib.max_degree(n, edges)}, is_valid(deg {q+3}, D 4) = {ok}')
    if ok:
        out = HERE / 'graphs' / f'as_deg3_q{q}_n{n}.json'
        out.write_text(json.dumps({'case': f'd{q+3}D4', 'value': n, 'output': [n, [list(e) for e in edges]]}))
        print('wrote', out)


if __name__ == '__main__':
    main()
