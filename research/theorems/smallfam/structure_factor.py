"""How much better than random are the record groups?  For a group given by a multiplication table, sample random
normal-form-free sets S = {e, s1, ..., s_{Delta-1}} and compute the exact number of uncovered targets (the hx cost:
D even: B-side within D-1 of (e,A); D odd: A-side from (e,A) plus B-side from (e,B)).  Compare with the
coupon-collector mean mu = (number of conditions) * N exp(-W/N) of SIZE_LAW.md, and with the observed fraction of
valid sets in the exhaustive runs.
Usage: python3 structure_factor.py TABLE DELTA D SAMPLES LABEL"""
import math
import random
import sys

import numpy as np

tab, Delta, D, M, label = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
L = open(tab).read().split('\n')
N, e = map(int, L[0].split())
T = np.array([list(map(int, L[1 + x].split())) for x in range(N)], dtype=np.int32)
INV = np.argmax(T == e, axis=1)


def uncovered(S, startB, targetA):
    dA = np.full(N, -1); dB = np.full(N, -1)
    if startB:
        dB[e] = 0; front, side = np.array([e]), 1
    else:
        dA[e] = 0; front, side = np.array([e]), 0
    for d in range(1, D):
        if side == 0:
            nb = np.unique(np.concatenate([T[s][front] for s in S])); nb = nb[dB[nb] < 0]; dB[nb] = d; side = 1
        else:
            nb = np.unique(np.concatenate([T[INV[s]][front] for s in S])); nb = nb[dA[nb] < 0]; dA[nb] = d; side = 0
        front = nb
        if len(front) == 0:
            break
    return int((dA < 0).sum()) if targetA else int((dB < 0).sum())


def cost(S):
    if D % 2 == 0:
        return uncovered(S, 0, 0)
    return uncovered(S, 0, 1) + uncovered(S, 1, 0)


if D % 2 == 0:
    W = sum(Delta * (Delta - 1) ** (l - 1) for l in range(1, D, 2)); nc = 1
else:
    W = 1 + sum(Delta * (Delta - 1) ** (l - 1) for l in range(2, D, 2)); nc = 2
mu = nc * N * math.exp(-W / N)
random.seed(11)
costs = []
for _ in range(M):
    S = [e] + random.sample([x for x in range(N) if x != e], Delta - 1)
    costs.append(cost(S))
costs.sort()
c = np.array(costs, dtype=float)
print(f'{label}: N={N} Delta={Delta} D={D} W={W} mu={mu:.1f}; random S ({M}): mean uncovered {c.mean():.1f} '
      f'(= {c.mean() / mu:.2f} mu), variance/mean {c.var() / max(c.mean(), 1e-9):.1f}, median {np.median(c):.0f}, '
      f'min {costs[0]}, 1st percentile {costs[max(0, M // 100 - 1)]}, P(cost <= mu/10) = {(c <= mu / 10).mean():.3f}; '
      f'Poisson(mu): variance/mean 1, P(valid) = e^-mu = {math.exp(-mu):.2e}')
