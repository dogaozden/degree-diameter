r"""
Diameter 5, the (7,5) record on 1,200 vertices: the Haar graph of G = SL(2,5) x Z_5 (order 600) with a connection set of
7 elements.   (research/beyond-haar-d5/records/d7D5_n1200_haar_sl5xc5.txt; checked there by research/frontier/build_haar2.py.)

Run:   sage d5_haar_7_5_1200.sage            (from this directory, or give the path: haar.sage is found next to this file)

The group.  The elements of G are the pairs ((a, b, c, d), z): (a, b, c, d) is the matrix with rows (a, b) and (c, d) over
GF(5) = Z/5 with a d - b c = 1, and z is in Z_5; the product is (M, z)(M', z') = (M M', z + z').  The vertices of the Haar graph are
    (0, ((a,b,c,d), z))   and   (1, ((a,b,c,d), z))        for ((a,b,c,d), z) in G,
and the edges are  (0, g) ~ (1, s g)  for the 7 elements s = (M_s, z_s) of S below (matrix product M_s M, sum z_s + z).
"""
import os, sys


def _load_here(name):
    try:
        here = os.path.dirname(os.path.abspath(__file__))
    except NameError:
        here = os.path.dirname(os.path.abspath(sys.argv[0])) if sys.argv and sys.argv[0] else os.getcwd()
    path = os.path.join(here, name)
    load(path if os.path.exists(path) else name)


_load_here('haar.sage')

P = 5
# the 7 elements of S: "mat(a,b,c,d) z=t" in the record file d7D5_n1200_haar_sl5xc5.txt
S_1200 = [((2, 1, 4, 0), 3), ((1, 3, 0, 1), 3), ((4, 4, 0, 4), 4), ((2, 3, 2, 1), 4),
          ((4, 3, 3, 0), 0), ((1, 2, 1, 3), 3), ((3, 3, 4, 1), 3)]


def sl2_times_cyclic(p=5):
    """All elements ((a,b,c,d), z) of SL(2,p) x Z_p: matrices over Z/p with det 1, z in Z/p."""
    return [((a, b, c, d), z) for a in range(p) for b in range(p) for c in range(p) for d in range(p)
            if (a * d - b * c) % p == 1 for z in range(p)]


def mul_sl2_cyclic(s, g, p=5):
    """The product s*g in SL(2,p) x Z_p: matrices multiply as 2x2 matrices (rows (a,b),(c,d)), the Z_p parts add."""
    (a, b, c, d), z = s
    (a2, b2, c2, d2), z2 = g
    return (((a * a2 + b * c2) % p, (a * b2 + b * d2) % p, (c * a2 + d * c2) % p, (c * b2 + d * d2) % p), (z + z2) % p)


def build_d5_haar_7_5_1200():
    """The Haar graph of SL(2,5) x Z_5 with the connection set S_1200: vertices (0, g), (1, g) with the group element
    g = (matrix, z) as label; edges (0,g) ~ (1, s g)."""
    els = sl2_times_cyclic(P)
    assert len(els) == 600 and all(len(set(x)) for x in [els])
    return haar_graph(None, S_1200, mul=lambda s, g: mul_sl2_cyclic(s, g, P), elements=els)


def check(q=5):
    G = build_d5_haar_7_5_1200()
    return report(G, 1200, 7, 5, name='(7,5): Haar graph of SL(2,5) x Z_5, |S| = 7')


if 'NO_AUTO_CHECK' not in globals():
    assert check()
