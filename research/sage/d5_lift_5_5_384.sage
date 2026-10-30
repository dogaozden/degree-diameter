r"""
Diameter 5, the (5,5) records on 384 vertices: regular lifts of a 4-vertex base graph by a group of order 96
(research/beyond-haar-d5b/records/; the file d5D5_n384_a1_g96_31.edges is the one kernel-checked in Lean).

Run:   sage d5_lift_5_5_384.sage

The groups are the small groups of order 96 of GAP, called from Sage as libgap.SmallGroup(96, i); they are realised as
permutation groups, and a voltage is named by its index in GAP's list Elements(G) (the identity is element 0), the same
numbering as the multiplication tables g96_31.txt, g96_17.txt of the records (check() verifies that the tables agree).
The labels of the vertices are the group elements (as permutations of the regular-permutation image of the group).

Base graph "a1" (SmallGroup(96,31), records d5D5_n384_a1_g96_31.sol, "SOL g 1 2 84 d 2 27 85 c 41"): the matrix [[1,4],[4,1]]
    A0 - B0   1 edge    voltage 0 (the identity)
    A0 - B1   4 edges   voltages 0, 1, 2, 84          ("g 1 2 84"; the identity completes the set)
    A1 - B0   4 edges   voltages 0, 2, 27, 85         ("d 2 27 85")
    A1 - B1   1 edge    voltage 41                    ("c 41")
Base graph "a2" (SmallGroup(96,17), d5D5_n384_a2_g96_17.sol, "SOL x 6 y 1 2 z 39 45 81 w 20"): the matrix [[2,3],[3,2]]
    A0 - B0   2 edges   voltages 0, 6
    A0 - B1   3 edges   voltages 0, 1, 2
    A1 - B0   3 edges   voltages 39, 45, 81
    A1 - B1   2 edges   voltages 0, 20
The lift has the vertices (0, 'A0', g), (0, 'A1', g), (1, 'B0', g), (1, 'B1', g), g in G, and for every base edge (a, b, v)
and g in G the edge (0, a, g) ~ (1, b, g v).  384 vertices, 5-regular.
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

# base edges (A vertex, B vertex, voltage index) of the records
BASE_A1_G96_31 = ([('A0', 'B0', 0)] + [('A0', 'B1', v) for v in (0, 1, 2, 84)] +
                  [('A1', 'B0', v) for v in (0, 2, 27, 85)] + [('A1', 'B1', 41)])
BASE_A2_G96_17 = ([('A0', 'B0', v) for v in (0, 6)] + [('A0', 'B1', v) for v in (0, 1, 2)] +
                  [('A1', 'B0', v) for v in (39, 45, 81)] + [('A1', 'B1', v) for v in (0, 20)])


def small_group_96(i):
    """SmallGroup(96, i) as (elements, mul): the elements of GAP's Elements(G) as permutations (via the regular-permutation
    isomorphism), in GAP's order (the identity first), and mul(h, g) = h*g."""
    G = libgap.SmallGroup(96, i)
    iso = G.IsomorphismPermGroup()
    P = PermutationGroup(gap_group=iso.Image())
    elems = [P(iso.Image(x)) for x in G.Elements()]
    assert elems[0] == P.one()
    return elems, (lambda h, g: h * g), G


def build_d5_lift_5_5_384(variant='a1_g96_31'):
    """variant 'a1_g96_31' (the Lean-checked record) or 'a2_g96_17'."""
    i, base = (31, BASE_A1_G96_31) if variant == 'a1_g96_31' else (17, BASE_A2_G96_17)
    elems, mul, G = small_group_96(i)
    return voltage_lift(elems, mul, [(a, b, elems[v]) for (a, b, v) in base])


def check(q=None):
    ok = True
    for variant, i in (('a1_g96_31', 31), ('a2_g96_17', 17)):
        elems, mul, G = small_group_96(i)
        info = str(libgap.StructureDescription(G))
        # the voltage indices mean GAP's Elements(G): compare with the record's multiplication table
        here = os.path.dirname(os.path.abspath(sys.argv[0])) if sys.argv and sys.argv[0] else os.getcwd()
        table = os.path.join(here, '..', 'beyond-haar-d5b', 'records', f'g96_{i}.txt')
        if os.path.exists(table):
            tab = [list(map(int, l.split())) for l in open(table).read().split('\n')[1:] if l.strip()]
            index = {e: k for k, e in enumerate(elems)}
            same = all(index[elems[a] * elems[b]] == tab[a][b] for a in range(96) for b in range(96))
            print(f'SmallGroup(96,{i}) = {info}: Cayley table equals the record table g96_{i}.txt: {same}')
            ok &= same
        G384 = build_d5_lift_5_5_384(variant)
        ok &= report(G384, 384, 5, 5, name=f'(5,5): lift by SmallGroup(96,{i}), {variant}')
    return ok


if 'NO_AUTO_CHECK' not in globals():
    assert check()
