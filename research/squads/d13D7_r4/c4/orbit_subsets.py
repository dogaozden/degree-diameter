#!/usr/bin/env python3
"""Card c4 (squad round 4): for every union T of the 16 S-orbits: |points(T)|, number of outside points freed by
removing T (sig(y) subset of T) and the candidate-set size |C(T)| = |points(T)| + freed.  Prints the T with the
smallest candidate sets among those with freed > 0, and the summary by |T|."""
import sys, os
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L

lab = np.load(os.path.join(HERE, 'lab720.npy'))
labs_S = np.load(os.path.join(HERE, 'labs_S720.npy'))
sig = np.load(os.path.join(HERE, 'sig720.npy'))
sizes = np.bincount(lab)
osz = np.array([sizes[l] for l in labs_S.tolist()], np.int64)
K = len(osz)
full = (1 << K) - 1
hist = np.bincount(sig[sig > 0], minlength=1 << K).astype(np.int64)
# zeta transform: f[T] = sum_{s subset of T} hist[s]
f = hist.copy()
for i in range(K):
    bit = 1 << i
    idx = np.arange(1 << K)
    sel = (idx & bit) != 0
    f[sel] += f[idx[sel] ^ bit]
# points(T)
pts = np.zeros(1 << K, np.int64)
for i in range(K):
    bit = 1 << i
    idx = np.arange(1 << K)
    pts[(idx & bit) != 0] += osz[i]
cand = pts + f
print('S orbit sizes', osz.tolist(), 'total', int(osz.sum()))
print('number of distinct sig values', int((hist > 0).sum()))
best = []
for T in range(1, 1 << K):
    if f[T] > 0:
        best.append((int(cand[T]), T, int(pts[T]), int(f[T])))
best.sort()
print('subsets T with freed > 0:', len(best))
print('smallest candidate sets (|C|, T, |points(T)|, freed):')
for row in best[:25]:
    print(row, 'orbits', [i for i in range(K) if row[1] >> i & 1])
np.save(os.path.join(HERE, 'freed_T.npy'), f)
np.save(os.path.join(HERE, 'pts_T.npy'), pts)
