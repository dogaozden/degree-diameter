# Writes relaxed.c input for G = W(9): per point, its collinear neighbours with flag 1 if the joining line is in S.
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from gqlib import W, regular_spread_W
G = W(9)
S = set(regular_spread_W(G))
n = G.np
with open('/home/user/degree-diameter/research/squads/gqd5-r2/c1/in_W9.txt', 'w') as f:
    f.write(f"{n}\n")
    for p in range(n):
        items = []
        for L in G.plines[p]:
            for r in G.lines[L]:
                if r != p:
                    items.append((r, 1 if L in S else 0))
        f.write(str(len(items)) + " " + " ".join(f"{r} {fl}" for r, fl in items) + "\n")
print("ok", n, len(S))
