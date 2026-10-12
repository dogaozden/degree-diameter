"""Araujo-Pardo--Lopez graph with vertex names (same ids as lib.araujo_lopez_graph).

Names: ('pt',x,y) affine point (x,y); ('P',m) point at infinity of slope m; ('P',) the vertical
point; ('ln',m,b) line y=mx+b; ('L',c) vertical line x=c; ('L',) line at infinity;
extra points ('Q0',), ('hp',j); extra lines ('M0',), ('hl',j), j in {0,1,a}.
"""
import sys
sys.path.insert(0, '/Users/dogaozden/AI_Projects/math/problems/bipartite_dd')
import lib


def al_named(q, a=2):
    F = lib.GF(q)
    ids = {}
    edges = set()

    def vid(name):
        return ids.setdefault(name, len(ids))

    def add(point, line):
        edges.add((vid(point), vid(line)))

    for m in range(q):
        for b in range(q):
            for x in range(q):
                add(("pt", x, F.add(F.mul(m, x), b)), ("ln", m, b))
    for m in range(q):
        add(("P", m), ("L",))
        for b in range(q):
            add(("P", m), ("ln", m, b))
    for c in range(q):
        add(("P",), ("L", c))
        for y in range(q):
            add(("pt", c, y), ("L", c))
    add(("P",), ("L",))
    edges.discard((vid(("pt", 0, a)), vid(("ln", 0, a))))
    J = (0, 1, a)
    I = [i for i in range(q) if i not in (0, 1)]
    add(("P",), ("M0",))
    add(("Q0",), ("L",))
    for j in J:
        add(("Q0",), ("hl", j))
        add(("hp", j), ("M0",))
    for i in I:
        add(("Q0",), ("ln", 0, i))
        add(("pt", 0, i), ("M0",))
    add(("P", 0), ("hl", a))
    add(("hp", a), ("L", 0))
    add(("hp", 0), ("hl", 1))
    add(("hp", 1), ("hl", 0))
    for j in J:
        for t in range(q):
            add(("hp", j), ("ln", t, j))
            add(("hl", j), ("pt", t, j))
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
    names = {i: nm for nm, i in ids.items()}
    return len(ids), sorted(edges), names, F
