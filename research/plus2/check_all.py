"""Run the +2 construction for every ordered choice of X0, X1, Xa, Xc on ell \\ {P}
(q <= 9), or a random sample (q > 9), with A, ell, P fixed.  PGL(3,q) is transitive on
(anti-flag, point of ell) triples, so for PG(2,q) this covers every input for q <= 9."""
import itertools
import random
import sys

from construction import pg_plane, default_frame, build, lib

for q in [int(x) for x in sys.argv[1:]]:
    pts, lns = pg_plane(q)
    A, ell, P, _ = default_frame(pts, lns)
    others = sorted(lns[ell] - {P})
    tuples = list(itertools.permutations(others, 4))
    if q > 9:
        tuples = random.Random(q).sample(tuples, 300)
    bad = 0
    for X in tuples:
        n, e = build(pts, lns, q, A, ell, P, list(X), regular=False)
        if not lib.is_valid(n, e, q + 2, 3):
            bad += 1
    print(f'q={q}: {len(tuples)} choices of (X0,X1,Xa,Xc), n={n}, invalid: {bad}', flush=True)
