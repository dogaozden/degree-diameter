import sys
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/r1/c42")
from build import write_bin, check_group
from math import gcd
import groups

def affine_ring(m):
    """AGL(1, Z_m) = {x -> a x + b : a in Z_m^*, b in Z_m}, order m*phi(m); identity index 0."""
    units = [a for a in range(1, m) if gcd(a, m) == 1]
    elems = [(0, 1)] + [(b, a) for b in range(m) for a in units if (b, a) != (0, 1)]
    idx = {e: i for i, e in enumerate(elems)}
    N = len(elems)
    T = np.empty((N, N), dtype=np.uint16)
    for i, (b, a) in enumerate(elems):
        T[i] = [idx[((b + a * b2) % m, (a * a2) % m)] for (b2, a2) in elems]
    return T

if __name__ == "__main__":
    out, which = sys.argv[1], sys.argv[2]
    if which.startswith("agl"):
        T = affine_ring(int(which[3:]))
    else:
        T = groups.table(which)
    check_group(T, which)
    write_bin(T, out)
