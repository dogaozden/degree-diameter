"""Root elements of G2(q) in the gh_build model, for any odd prime q (patterns found by g2_roots.py at q = 3,
coefficients re-fitted at the given q). Exposes root_elements(q) -> list of (name, t, 7x7 matrix)."""
import itertools
import json
import sys

import numpy as np

from lift import ROOT
sys.path.insert(0, str(ROOT / 'research' / 'gh6'))
import gh_build  # noqa: E402

LONG = [((0, 1), (5, 4)), ((0, 2), (6, 4)), ((1, 0), (4, 5)), ((1, 2), (6, 5)), ((2, 0), (4, 6)), ((2, 1), (5, 6))]
SHORT = [((0, 3), (3, 4), (5, 2), (6, 1)), ((0, 5), (1, 4), (3, 2), (6, 3)), ((0, 6), (2, 4), (3, 1), (5, 3)),
         ((1, 3), (3, 5), (4, 2), (6, 0)), ((1, 6), (2, 5), (3, 0), (4, 3)), ((2, 3), (3, 6), (4, 1), (5, 0))]


class Hex:
    def __init__(self, q):
        self.q = q
        hexfile = ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json'
        self.lines = json.loads(hexfile.read_text())['lines'] if hexfile.exists() else gh_build.hexagon(q)[1]
        self.P = gh_build.quadric_points(q)
        self.idx = {p: i for i, p in enumerate(self.P)}
        self.lineset = {frozenset(L): k for k, L in enumerate(self.lines)}
        self.Pa = np.array(self.P, dtype=np.int64)

    def point_perm(self, M):
        img = (self.Pa @ M.T) % self.q
        out = []
        for v in img:
            try:
                out.append(self.idx[gh_build.normalize(tuple(int(x) for x in v), self.q)])
            except (KeyError, ValueError):
                return None
        return out

    def line_perm(self, pp):
        out = []
        for L in self.lines:
            k = self.lineset.get(frozenset(pp[p] for p in L))
            if k is None:
                return None
            out.append(k)
        return out


def mat(q, units, coefs):
    N = np.zeros((7, 7), dtype=np.int64)
    for (i, j), c in zip(units, coefs):
        N[i, j] = c % q
    inv2 = pow(2, q - 2, q)
    return (np.eye(7, dtype=np.int64) + N + inv2 * (N @ N)) % q


def fit(H):
    """For each root pattern find coefficients (first unit = 1) giving an automorphism; return list of
    (pattern, coefs)."""
    q = H.q
    out = []
    for pat in LONG + SHORT:
        for rest in itertools.product(range(1, q), repeat=len(pat) - 1):
            coefs = (1,) + rest
            M = mat(q, pat, coefs)
            pp = H.point_perm(M)
            if pp is not None and H.line_perm(pp) is not None:
                out.append((pat, coefs))
                break
        else:
            out.append((pat, None))
    return out


if __name__ == '__main__':
    q = int(sys.argv[1])
    H = Hex(q)
    for pat, c in fit(H):
        print(pat, c)
