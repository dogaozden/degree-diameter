r"""
Diameter 5, the (5,5) record on 360 vertices: the regular lift of the base graph [[2,3],[3,2]] by the group
C15 x S3 (SmallGroup(90,6)).   (research/beyond-haar-d5/records/build_d5D5_n360_z15s3.py, d5D5_n360_lift_g90_6.edges.)

Run:   sage d5_lift_5_5_360.sage

The group.  The elements of C15 x S3 are the pairs (t, p), t in Z_15 and p a permutation of {1,2,3} written as the tuple of
the images (p(1), p(2), p(3)); the product is (t, p)(s, r) = (t + s, p r), with GAP's convention i^(p r) = (i^p)^r
(first p, then r).  The labels of the vertices are the group elements.
The base graph.  Four vertices: A0, A1 (side 0) and B0, B1 (side 1); the base edges (the numbers are the multiplicities
in the matrix [[2,3],[3,2]]):
    A0 - B0   2 edges   voltages (0, id) and (6, (3 2 1))                      [(3,2,1) is the transposition (1 3)]
    A0 - B1   3 edges   voltages (0, id), (10, (3,2,1)) and (12, (1,3,2))      [(1,3,2) is the transposition (2 3)]
    A1 - B0   3 edges   voltages (0, (3,2,1)), (1, (1,3,2)), (9, (1,3,2))
    A1 - B1   2 edges   voltages (0, id) and (6, (3,2,1))
The lift has the vertices (0, 'A0', g), (0, 'A1', g), (1, 'B0', g), (1, 'B1', g), g in C15 x S3, and for every base
edge (a, b, v) and every g the edge (0, a, g) ~ (1, b, g v).  360 vertices, 5-regular.
"""
import os, sys
from itertools import permutations


def _load_here(name):
    try:
        here = os.path.dirname(os.path.abspath(__file__))
    except NameError:
        here = os.path.dirname(os.path.abspath(sys.argv[0])) if sys.argv and sys.argv[0] else os.getcwd()
    path = os.path.join(here, name)
    load(path if os.path.exists(path) else name)


_load_here('haar.sage')

ID, T13, T23 = (1, 2, 3), (3, 2, 1), (1, 3, 2)       # the images of 1, 2, 3 under the identity and the transpositions (1 3), (2 3)


def c15_times_s3():
    return [(t, p) for t in range(15) for p in permutations((1, 2, 3))]


def mul_c15_s3(g, v):
    """(t, p)(s, r) = (t + s mod 15, p r) where p r is "first p, then r": i -> r(p(i))."""
    (t, p), (s, r) = g, v
    return ((t + s) % 15, tuple(r[p[i] - 1] for i in range(3)))


def base_360():
    """The base edges (a, b, voltage) of [[2,3],[3,2]] with the voltages of the record."""
    return ([('A0', 'B0', (0, ID)), ('A0', 'B0', (6, T13))] +
            [('A0', 'B1', (0, ID)), ('A0', 'B1', (10, T13)), ('A0', 'B1', (12, T23))] +
            [('A1', 'B0', (0, T13)), ('A1', 'B0', (1, T23)), ('A1', 'B0', (9, T23))] +
            [('A1', 'B1', (0, ID)), ('A1', 'B1', (6, T13))])


def build_d5_lift_5_5_360():
    els = c15_times_s3()
    assert len(els) == 90
    return voltage_lift(els, mul_c15_s3, base_360())


def check(q=None):
    G = build_d5_lift_5_5_360()
    return report(G, 360, 5, 5, name='(5,5): lift of [[2,3],[3,2]] by C15 x S3')


if 'NO_AUTO_CHECK' not in globals():
    assert check()
