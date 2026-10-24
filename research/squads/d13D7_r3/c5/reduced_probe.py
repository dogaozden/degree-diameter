# c5: probe the reduced problem (lines in direction u + one lift per cone class) for the 25-line set of the 397 config.
import struct, sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/d13D7_r3/c5")
import numpy as np
from cone_reduce import co, classes, reduce_count, Bmat, p
def line_offsets(path):
    return [tuple(int(t) for t in l.split()) for l in open(path) if l.strip() and not l.startswith('#')]
def qp(a, b, c, e, f):
    return (c * c - a * e - b * f) % p
# all 14641 lines with a=0 (coset reps)
reps = [(0, b, c, e, f) for b in range(p) for c in range(p) for e in range(p) for f in range(p)]
def compat_line(t, s):
    d = [(t[i] - s[i]) % p for i in range(5)]
    lam0 = (-d[0]) % p
    d = [(d[i] + lam0 * (1, 0, 0, 9, 0)[i]) % p for i in range(5)]
    return all(qp(d[0] + lam * 1, d[1], d[2], d[3] + lam * 9, d[4]) != 0 for lam in range(p))
K = line_offsets(sys.argv[1])
print('lines in K', len(K))
usable = reduce_count(K)
m0 = len(usable)
print('m(K) =', m0, ' f =', 11 * len(K) + m0)
free = [t for t in reps if t not in K and all(compat_line(t, s) for s in K)]
print('free lines (compatible with all of K):', len(free))
best = None
res = []
for t in free:
    r = reduce_count(K + [t])
    res.append((11 * (len(K) + 1) + len(r), t, len(r)))
res.sort(reverse=True)
print('best ADD results (f, line, m):', res[:5])
