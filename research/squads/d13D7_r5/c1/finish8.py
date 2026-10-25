#!/usr/bin/env python3
"""finish8.py (card c1, squad round 5): greedy fill of a pairwise-opposite point set of H(8) with single points.
usage: finish8.py IN_IDX_FILE OUT_IDX_FILE
Repeatedly adds a point opposite to every current member, choosing the candidate that blocks the fewest other
candidates (ties by index).  Verifies the result (pairwise opposite, no repeats) before writing.
"""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orb8 as L  # noqa: E402


def fill(idx):
    S = [int(x) for x in idx]
    inS = np.zeros(L.N, bool)
    inS[S] = True
    cand = ~inS
    for s in S:
        cand &= L.bdot(L.P[s], L.P) != 0
    added = []
    while cand.any():
        cs = np.flatnonzero(cand)
        X = L.P[cs]
        Bm = L.bdot(X[:, None, :], X[None, :, :])
        nb = (Bm == 0).sum(axis=1) - 1            # candidates blocked by this one (excluding itself)
        pick = int(cs[int(np.argmin(nb))])
        S.append(pick)
        added.append(pick)
        cand[pick] = False
        cand &= L.bdot(L.P[pick], L.P) != 0
    return S, added


if __name__ == '__main__':
    src, dst = sys.argv[1], sys.argv[2]
    idx = [int(x) for x in open(src) if x.strip() and not x.startswith('#')]
    S, added = fill(idx)
    assert L.pairwise_ok(S), 'fill produced an invalid set'
    with open(dst, 'w') as f:
        f.write(f'# {len(S)} points, pairwise opposite ({len(idx)} from the orbit union + {len(added)} greedy fill)\n')
        f.write('\n'.join(map(str, sorted(S))) + '\n')
    print(f'in {len(idx)} fill +{len(added)} out {len(S)}')
