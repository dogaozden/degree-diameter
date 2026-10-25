#!/usr/bin/env python3
"""Independent check of a point set of Q(6,q): every point singular for Q = x0x4+x1x5+x2x6-x3^2, points pairwise
distinct (projectively) and pairwise non-orthogonal (= pairwise opposite in H(q)).  usage: checkset.py FILE [q]"""
import sys, numpy as np
q = int(sys.argv[2]) if len(sys.argv) > 2 else 11
X = np.loadtxt(sys.argv[1], dtype=np.int64, comments='#', ndmin=2) % q
inv = np.array([0] + [pow(i, q - 2, q) for i in range(1, q)])
first = np.argmax(X != 0, axis=1); assert np.all(X[np.arange(len(X)), first] != 0), 'zero vector'
X = X * inv[X[np.arange(len(X)), first]][:, None] % q
sing = (X[:, 0] * X[:, 4] + X[:, 1] * X[:, 5] + X[:, 2] * X[:, 6] - X[:, 3] ** 2) % q == 0
distinct = len({tuple(r) for r in X}) == len(X)
Y = X[:, [4, 5, 6, 3, 0, 1, 2]].copy(); Y[:, 3] = (-2 * Y[:, 3]) % q
Bm = (X @ Y.T) % q
np.fill_diagonal(Bm, 1)
nonorth = bool(np.all(Bm != 0))
ok = bool(sing.all()) and distinct and nonorth
print(f"{'RESULT VALID' if ok else 'RESULT INVALID'} n={len(X)} singular={bool(sing.all())} distinct={distinct} "
      f"pairwise_nonorthogonal={nonorth} orthogonal_pairs={int((Bm == 0).sum() // 2)}")
