"""Candidate clean "+2" rule: the Araujo-Pardo--Lopez graph with a fourth hat pair.

Names as in al.py. S = {0, 1, a, c} are the hatted rows.
"""
import sys
sys.path.insert(0, '/Users/dogaozden/AI_Projects/math/problems/bipartite_dd')
import lib


def plus2_named(q, a=2, c=None, variant=0):
    F = lib.GF(q)
    if c is None:
        c = next(x for x in range(q) if x not in (0, 1, a))
    ids = {}
    edges = set()

    def vid(name):
        return ids.setdefault(name, len(ids))

    def add(point, line):
        edges.add((vid(point), vid(line)))

    def rem(point, line):
        edges.remove((vid(point), vid(line)))

    for m in range(q):
        for b in range(q):
            for x in range(q):
                add(("pt", x, F.add(F.mul(m, x), b)), ("ln", m, b))
    for m in range(q):
        add(("P", m), ("L",))
        for b in range(q):
            add(("P", m), ("ln", m, b))
    for cc in range(q):
        add(("P",), ("L", cc))
        for y in range(q):
            add(("pt", cc, y), ("L", cc))
    add(("P",), ("L",))
    S = (0, 1, a, c)
    rem(("pt", 0, a), ("ln", 0, a))
    # rotation on the vertical line x=0 and the horizontal lines y=0,1,c
    for y in (0, 1, c):
        rem(("pt", 0, y), ("ln", 0, y))
    add(("pt", 0, 1), ("ln", 0, 0))
    add(("pt", 0, c), ("ln", 0, 1))
    add(("pt", 0, 0), ("ln", 0, c))
    T = [i for i in range(q) if i not in (0, 1, c)]
    add(("P",), ("M0",))
    add(("Q0",), ("L",))
    for s in S:
        add(("Q0",), ("hl", s))
        add(("hp", s), ("M0",))
        for t in range(q):
            add(("hp", s), ("ln", t, s))
            add(("hl", s), ("pt", t, s))
    for i in T:
        add(("Q0",), ("ln", 0, i))
        add(("pt", 0, i), ("M0",))
    add(("P", 0), ("hl", a))
    add(("hp", a), ("L", 0))
    add(("hp", 0), ("hl", c))
    add(("hp", c), ("hl", 1))
    add(("hp", 1), ("hl", 0))
    degree = {}
    for u, v in edges:
        degree[u] = degree.get(u, 0) + 1
        degree[v] = degree.get(v, 0) + 1
    matching = [(("P", i), ("L", i)) for i in range(q)]
    matching += [(("pt", x, y), ("ln", x, y)) for x in range(q) for y in range(q)]
    for point, line in matching:
        u, v = vid(point), vid(line)
        if degree.get(u) == q + 1 and degree.get(v) == q + 1:
            edges.add((u, v))
            degree[u] += 1
            degree[v] += 1
    names = {i: nm for nm, i in ids.items()}
    return len(ids), sorted(edges), names, degree


if __name__ == '__main__':
    for q in [int(x) for x in sys.argv[1:]]:
        n, e, names, deg = plus2_named(q)
        low = [names[v] for v in range(n) if deg.get(v, 0) < q + 2]
        print(q, n, 'maxdeg', max(deg.values()), 'low-degree', len(low), low[:6],
              'bad pairs', lib.bad_pairs(n, e, 3), 'valid', lib.is_valid(n, e, q + 2, 3))
