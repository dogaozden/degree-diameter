#!/usr/bin/env python3
"""Family c17: S = O(X) u O(Y) in SL(2,q), 3+3 type, with a Z_m label on each element.
usage: gen17.py q m X(a,b,c,d) Y(a,b,c,d) mode
  mode E: alpha-equivariant labels (x,z)->(w x w^-1, r z), r a cube root of unity mod m; X gets t=1, Y gets t=2
  mode N: labels z(M) = dlog_g(first nonzero entry of M) mod m (g primitive root mod q); no symmetry
  mode Z: all labels 0 (m-independent control)"""
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/thmfam-r1/c17')
from common17 import orbit, primroot, cuberoot
q, m = int(sys.argv[1]), int(sys.argv[2])
X = tuple(map(int, sys.argv[3].split(','))); Y = tuple(map(int, sys.argv[4].split(',')))
mode = sys.argv[5]
def red(M): return tuple(x % q for x in M)
lines = []
if mode == 'E':
    r = cuberoot(m) if m > 1 else 0
    if m > 1 and r is None: sys.exit('m must be prime = 1 mod 3')
    tX = 1 % m if m > 1 else 0
    tY = 2 % m if m > 1 else 0   # fixed label for the Y orbit (2 is not in {1,r,r^2} for m=19,31,37,43,61)
    for i, M in enumerate(orbit(X)):
        lines.append('%d %d %d %d %d' % (*red(M), (tX * pow(r, i, m) if m > 1 else 0) % m if m > 1 else 0))
    for i, M in enumerate(orbit(Y)):
        lines.append('%d %d %d %d %d' % (*red(M), (tY * pow(r, i, m)) % m if m > 1 else 0))
elif mode == 'N':
    g = primroot(q)
    import math
    from math import log
    dl = {}; x = 1
    for e in range(q - 1): dl[x] = e; x = x * g % q
    for M in orbit(X) + orbit(Y):
        R = red(M); e = next(v for v in (R[1], R[2], R[0], R[3]) if v)
        lines.append('%d %d %d %d %d' % (*R, dl[e] % m))
else:
    for M in orbit(X) + orbit(Y):
        lines.append('%d %d %d %d %d' % (*red(M), 0))
print('\n'.join(lines))
