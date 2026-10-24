"""Build the route-chart lift of a coloured controller and write it in apsp.c format.
usage: python3 lift.py CONTROLLER(.json|.edges|.ctrl) CHART.txt q k out.edges [colouring-seed]
A-vertex (a, x) -> a * q^4 + code(x); B-vertex (b, y) -> m q^4 + b q^4 + code(y); code(x) = sum x_i q^i."""
import sys, itertools
from chartlib import read_chart_txt
from controller import read_graph, proper_colouring

def build(ch, m, cedges):
    F, q, n = ch.F, ch.q, ch.n; Q = q ** n
    vecs = list(itertools.product(range(q), repeat=n))
    code = lambda v: sum(c * q ** i for i, c in enumerate(v))
    # per colour: image table x -> A_c x, and the lines lam b_c
    img = [[code(F.matvec(ch.A[c], x)) for x in vecs] for c in range(ch.k)]
    lines = [[F.vscale(l, ch.b[c]) for l in range(q)] for c in range(ch.k)]
    E = []
    for (a, bb, c) in cedges:
        for xi, x in enumerate(vecs):
            y0 = F.matvec(ch.A[c], x)
            for v in lines[c]:
                E.append((a * Q + code(x), m * Q + bb * Q + code(F.vadd(y0, v))))
    return 2 * m * Q, E

if __name__ == '__main__':
    path, chartp, q, k, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    seed = int(sys.argv[6]) if len(sys.argv) > 6 else 0
    if path.endswith('.ctrl'):          # "m" then lines "a b colour" (from ctrl_search.c)
        rows = [list(map(int, l.split())) for l in open(path) if l.strip()]
        m = rows[0][0]; ce = [tuple(x) for x in rows[1:]]; As = list(range(m))
    else:
        n, E = read_graph(path)
        As, Bs, ce = proper_colouring(n, E, k, seed)
    ch = read_chart_txt(chartp, q, k)
    N, LE = build(ch, len(As), ce)
    assert len(set(LE)) == len(LE), 'repeated edge'
    with open(out, 'w') as f:
        f.write('%d\n' % N); f.writelines('%d %d\n' % e for e in LE)
    print('controller', path, 'm =', len(As), 'lift vertices', N, 'edges', len(LE))
