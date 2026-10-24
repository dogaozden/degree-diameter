"""The Hermitian spread of H(q): the q^3+1 lines of H(q) contained in an elliptic hyperplane section n^perp of Q(6,q)
(n = (1,0,0,0,a,0,0) with -a a non-square).  Lines in it are pairwise opposite.  Writes their indices to stdout."""
import numpy as np, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import hexlib
q, lines, coord = hexlib.load()
sq = {(x * x) % q for x in range(1, q)}
a = next(a for a in range(1, q) if (-a) % q not in sq)
n = np.array([1, 0, 0, 0, a, 0, 0])
onperp = hexlib.bilinear(coord, n[None, :], q) == 0
inside = onperp[lines].all(axis=1)
S = np.nonzero(inside)[0]
print(f'# a={a}: {len(S)} lines inside n^perp (q^3+1 = {q**3 + 1})', file=sys.stderr)
for l in S: print(l)
