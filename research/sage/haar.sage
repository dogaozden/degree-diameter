r"""
Helpers for the group-based records (diameter 5): Haar graphs and regular voltage lifts.

    haar_graph(G, S)          the Haar graph of the group G with connection set S
    voltage_lift(G, base)     the regular lift of a bipartite base multigraph with voltages in G
    report(...)               the final printout used by every check(q)

Loaded by d5_haar_7_5_1200.sage, d5_lift_5_5_360.sage and d5_lift_5_5_384.sage.

Haar graph of a group G with connection set S (research/frontier/build_haar2.py, docstring):
    vertices  (0, g) and (1, g), g in G   (the two copies of G; "A" side = 0, "B" side = 1)
    edges     (0, g) ~ (1, s*g)           for g in G, s in S
Right multiplication by G is an automorphism group that is regular on each side.  The graph has 2|G| vertices and is
|S|-regular when the elements of S are distinct.

Voltage lift.  A base bipartite multigraph has vertices on the A side and on the B side and edges (a, b, v) with
a voltage v in G.  The lift has the vertices (0, a, h) and (1, b, h), h in G, and for every base edge (a, b, v) and
h in G the edge (0, a, h) ~ (1, b, h*v)  (research/beyond-haar-d5/exh/b4a2x_edges.py).  A Haar graph is the
lift of the base with one A vertex, one B vertex and the edges (A, B, s^-1)...; here the Haar graph is built directly.
"""


def haar_graph(G, S, mul=None, elements=None):
    r"""
    The Haar graph of G with connection set S: vertices (0, g) and (1, g), edges (0, g) ~ (1, s*g), s in S.

    G         a Sage group (iterable, elements multiply with *), or any finite set of elements together with ...
    S         the connection set (a list of distinct elements of G)
    mul       optional function mul(s, g) = the product s*g (default: s * g)
    elements  optional list of the elements of G (default: list(G))
    The labels are the group elements themselves.
    """
    els = list(G) if elements is None else list(elements)
    prod = mul if mul is not None else (lambda s, g: s * g)
    assert len(set(S)) == len(S), 'the elements of S must be distinct'
    H = Graph(multiedges=False, loops=False)
    H.add_vertices([(0, g) for g in els] + [(1, g) for g in els])
    for g in els:
        for s in S:
            # (0,g) ~ (1, s g): the edge of the generator s at g
            H.add_edge((0, g), (1, prod(s, g)))
    return H


def voltage_lift(elements, mul, base):
    r"""
    The regular lift with voltages in a group.
    elements  list of the elements of the group (these are used as labels)
    mul       mul(h, v) = the product h*v
    base      list of base edges (a, b, v): a an A-side base vertex name, b a B-side base vertex name, v a group element
    Vertices (0, a, h) and (1, b, h); for every base edge (a, b, v) and every h the edge (0, a, h) ~ (1, b, h*v).
    """
    H = Graph(multiedges=False, loops=False)
    for (a, b, v) in base:
        for h in elements:
            u, w = (0, a, h), (1, b, mul(h, v))
            assert not H.has_edge(u, w), 'repeated edge (two equal voltages on parallel base edges)'
            H.add_edge(u, w)
    return H


def report(G, expect_n, expect_deg, expect_diam, bip=True, name='', regular=False):
    n = G.order()
    maxdeg = max(G.degree())
    isbip = G.is_bipartite()
    diam = G.diameter()
    ok = (n == expect_n and maxdeg == expect_deg and isbip == bip and diam == expect_diam)
    reg = (min(G.degree()) == maxdeg)
    print(f'{name}: vertices {n} (expected {expect_n}), max degree {maxdeg} (expected {expect_deg}), '
          f'bipartite {isbip}, diameter {diam} (expected {expect_diam}){", regular" if reg else ""}  ->  {"OK" if ok else "MISMATCH"}')
    return ok
