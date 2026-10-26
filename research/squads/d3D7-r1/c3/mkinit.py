import sys, json
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d3D7-r1/c3')
from gadget import *
n0, E0 = relabel(*load('/home/user/degree-diameter/research/d3D7/seeds/conder168.edges'))
picks = [((0,84),(1,85)), ((0,105),(1,102)), ((2,86),(4,88)), ((3,87),(5,89)), ((1,127),(44,86))]
for k, (e1, e2) in enumerate(picks):
    n2, E2 = gadget(n0, E0, e1[0], e1[1], e2[0], e2[1])
    n2, E2 = relabel(n2, E2)
    c = cost(n2, E2)
    p = f'inits/p{k}.edges'; write(p, n2, E2)
    # check cubic bipartite
    from collections import Counter
    deg = Counter(); [deg.update([a, b]) for a, b in E2]
    assert all(deg[v] == 3 for v in range(n2)) and all(a < n2//2 <= b for a, b in E2)
    print(k, e1, e2, 'n', n2, 'cost', c, 'edges', len(E2))
