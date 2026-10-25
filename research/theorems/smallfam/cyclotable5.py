"""Delta=5 version of cyclotable4.py: for each k <= KMAX and o | k (o >= 2) with phi(o) <= PHIMAX, B(k, o) =
k * max_j min_J |W_J|, the largest N a Haar graph of any Z_p x|_r Z_k (p prime, ord r = o) of diameter D can have
(cyclobound.py, FIBER).
The bound is invariant under permuting (j_2, ..., j_4) (permuting the generators with formal parts, and their formal
coordinates, is an automorphism of the universal group), so patterns are also reduced by that symmetry.
Usage: python3 cyclotable5.py D KMAX [PHIMAX]"""
import itertools
import sys
from math import gcd
import cyclobound
cyclobound.FIBER = True
D, KMAX = int(sys.argv[1]), int(sys.argv[2])
PHIMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 2
phi = lambda n: sum(1 for x in range(1, n + 1) if gcd(x, n) == 1)
print(f'# Delta=5 D={D}: k o B(k,o) j_max   (phi(o) <= {PHIMAX})')


def canon(j, k):
    units = [u for u in range(1, k + 1) if gcd(u, k) == 1]
    return min((0, (u * j[1]) % k) + tuple(sorted((u * x) % k for x in p))
               for u in units for p in itertools.permutations(j[2:]))


for k in range(2, KMAX + 1):
    for o in range(2, k + 1):
        if k % o == 0 and phi(o) <= PHIMAX:
            reps = {canon(j, k): j for j in cyclobound.admissible_js(5, k, o)}
            b, bj = -1, None
            for j in reps.values():
                v = cyclobound.ball_bound(5, D, k, o, j)
                if v > b:
                    b, bj = v, j
            print(f'{k:3d} {o:3d} {b:7d} {bj}  ({len(reps)} patterns)', flush=True)
