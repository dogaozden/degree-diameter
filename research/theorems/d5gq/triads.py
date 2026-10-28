"""Triad centre counts (Section 1, fact (F5)): for pairwise non-collinear points x, y, z, the number of points
collinear with all three.  W(q): 1 or q+1 (all points regular); Q(4,q), q odd: 0 or 2 (antiregular)."""
import numpy as np, itertools, random
from gqlib import W, Q4
rng = random.Random(3)
for q in (3, 5, 7):
    for G in (W(q), Q4(q)):
        seen = set()
        for _ in range(3000):
            x = rng.randrange(G.np)
            far = np.nonzero(~G.col[x])[0]; far = far[far != x]
            y = int(rng.choice(far))
            far2 = [z for z in far if z != y and not G.col[y, z]]
            z = int(rng.choice(far2))
            seen.add(int((G.col[x] & G.col[y] & G.col[z]).sum()))
        print(G.name, 'triad centre counts seen (3000 random triads):', sorted(seen))
