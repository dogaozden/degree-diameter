"""Largest partial ovoid of W(5): fix two non-collinear points x, y (PSp(4,q) is transitive on such pairs) and find
the clique number of the non-collinearity graph on the points non-collinear with both. Writes the input for clique.c."""
import sys
from gf import GF
from gq import W
q = int(sys.argv[1]); Wq = W(GF(q)); N = Wq.N
x = 0; y = next(p for p in range(N) if p != x and p not in Wq.collinear[x])
V = [p for p in range(N) if p not in (x, y) and p not in Wq.collinear[x] and p not in Wq.collinear[y]]
print(len(V))
for a in V:
    print(''.join('1' if (b != a and b not in Wq.collinear[a]) else '0' for b in V))
