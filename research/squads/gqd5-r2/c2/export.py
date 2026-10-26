# export W(11) collinearity graph with forbidden flags (line in S) to graph.txt; also pickle S-line id per point
import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import numpy as np, gqlib
G = gqlib.W(11)
S = gqlib.regular_spread_W(G)
Sset = set(S)
n = G.np
sline = [-1]*n
for l in S:
    for p in G.lines[l]:
        assert sline[p] == -1
        sline[p] = l
assert min(sline) >= 0
with open('graph.txt', 'w') as f:
    f.write(f"{n}\n")
    for p in range(n):
        nb = []
        for l in G.plines[p]:
            for r in G.lines[l]:
                if r != p:
                    nb.append((r, 1 if l in Sset else 0))
        f.write(str(len(nb)) + " " + " ".join(f"{a} {b}" for a, b in nb) + "\n")
json.dump({'sline': sline, 'S': S, 'lines': [list(map(int, l)) for l in G.lines], 'plines': [list(map(int, x)) for x in G.plines]}, open('struct.json', 'w'))
print('n', n, 'nl', G.nl, 'S', len(S))
