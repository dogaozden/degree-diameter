"""Is the degree-filling matching needed for diameter 3?  Remove it and count bad pairs."""
import sys
sys.path.insert(0, str(__import__('pathlib').Path(__file__).resolve().parent))
from plus2 import plus2_named
from al import al_named
import lib


def matching_edges(n, e, names, q):
    out = []
    for u, v in e:
        a, b = names[u], names[v]
        if a[0] == 'pt' and b[0] == 'ln' and (a[1], a[2]) == (b[1], b[2]) and a[1] != 0:
            out.append((u, v))
        if a[0] == 'P' and b[0] == 'L' and len(a) == 2 and len(b) == 2 and a[1] == b[1]:
            # P_i - L_i is never a PG incidence
            out.append((u, v))
    return out


for q in [int(x) for x in sys.argv[1:]]:
    for label, (n, e, names, *_) in (('AL', al_named(q)), ('plus2', plus2_named(q))):
        M = set(matching_edges(n, e, names, q))
        core = [x for x in e if x not in M]
        print(q, label, 'matching edges', len(M), 'core bad pairs', lib.bad_pairs(n, core, 3))
