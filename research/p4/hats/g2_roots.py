"""Find root elements of G2(q) in the 7-dim model of research/gh6/gh_build.py by brute force:
maps I + N + N^2/2 with N = sum of up to 3 signed matrix units, that preserve the quadric and the set of H(q) lines.

python3 g2_roots.py q   -> prints the N found (as lists of (i, j, coefficient))
"""
import itertools
import json
import sys

import numpy as np

from lift import ROOT
sys.path.insert(0, str(ROOT / 'research' / 'gh6'))
import gh_build  # noqa: E402

q = int(sys.argv[1])
hexfile = ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json'
lines = json.loads(hexfile.read_text())['lines'] if hexfile.exists() else gh_build.hexagon(q)[1]
P = gh_build.quadric_points(q)
idx = {p: i for i, p in enumerate(P)}
lineset = {frozenset(L) for L in lines}
Pa = np.array(P, dtype=np.int64)
inv2 = pow(2, q - 2, q)


def apply(M):
    img = (Pa @ M.T) % q
    out = []
    for v in img:
        try:
            out.append(idx[gh_build.normalize(tuple(int(x) for x in v), q)])
        except (KeyError, ValueError):
            return None
    return out


def is_aut(M):
    im = apply(M)
    if im is None:
        return False
    return all(frozenset(im[p] for p in L) in lineset for L in lines)


found = []
units = [(i, j) for i in range(7) for j in range(7) if i != j]
R = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else [1, 2]
for r in R:
    for combo in itertools.combinations(units, r):
        if r >= 3 and not (sum(1 for i, j in combo if j == 3) == 1 and sum(1 for i, j in combo if i == 3) == 1):
            continue
        for signs in itertools.product(range(1, q), repeat=r):
            N = np.zeros((7, 7), dtype=np.int64)
            for (i, j), s in zip(combo, signs):
                N[i, j] = s
            if np.any(np.linalg.matrix_power(N, 3) % q):
                continue
            M = (np.eye(7, dtype=np.int64) + N + inv2 * (N @ N)) % q
            if is_aut(M):
                found.append([(i, j, int(s)) for (i, j), s in zip(combo, signs)])
print(len(found), 'root-type elements with <= 2 units:')
for f in found:
    print(f)
