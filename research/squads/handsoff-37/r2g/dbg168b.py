import sys
sys.argv = ['x']
exec(open('calib168.py').read().split("comp = Comp(S, [0], [0])")[0])
comp = Comp(S, [0], [0])
from collections import Counter
big = [i for i, e in enumerate(comp.edges) if len(e[4]) == 252]
for i in big[:27]:
    nn, adj, ev = comp.graph([i])
    deg = Counter(len(a) for a in adj)
    print(i, 'deg', dict(deg), 'far', far_count(nn, adj), 'distinct edges', len(set(map(tuple, map(sorted, ev)))), end=' | ')
print()
# compare: vertex-level orbit of conder edge (0, N[0][0]) under H
e0 = (0, N[0][0]); orbit = set()
for p in H:
    a, b = p[0], p[e0[1]]
    orbit.add((min(a,b), max(a,b)))
print('vertex-level H-orbit of a conder edge:', len(orbit))
