"""Fraction of collinear point pairs {u, w} of H(q) whose images under a bijection s: points -> lines are concurrent
(distance 2), at distance 4, or opposite (distance 6).  usage: nearfrac.py q matching.txt|random [seed]"""
import sys
import random
import numpy as np
import gh
q = int(sys.argv[1])
H = gh.load(q); N = H.N
Dm, _ = gh.distances(H)
if sys.argv[2] == 'random':
    s = np.array(random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1).sample(range(N), N))
else:
    s = np.array([int(l) for l in open(sys.argv[2]) if l.strip()])
U, W = np.nonzero(np.triu(Dm[:N, :N] == 2))
d = Dm[N + s[U], N + s[W]]
print(f'q {q} {sys.argv[2]}: collinear pairs {len(U)}; images concurrent {np.mean(d == 2):.4f}, at distance 4 '
      f'{np.mean(d == 4):.4f}, opposite {np.mean(d == 6):.4f}')
