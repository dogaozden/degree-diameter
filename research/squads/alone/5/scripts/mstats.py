# edges between N(b*) and N(a*), max matching size, grouped by dist(a*, b*)
import random
from graph import load
from twin import matching
n, adj, E = load('base.e'); nA = n // 2
rnd = random.Random(0)
def dist_side(a):
    d = {a: 0}; fr = [a]; k = 0
    while fr:
        k += 1; nf = []
        for x in fr:
            for y in adj[x]:
                if y not in d: d[y] = k; nf.append(y)
        fr = nf
    return d
a = 0
D = dist_side(a)
bycls = {}
for b in range(nA, n):
    bycls.setdefault(D[b], []).append(b)
for dd in sorted(bycls):
    for b in rnd.sample(bycls[dd], 3):
        NA = set(adj[a]); NBs = set(adj[b])
        cnt = sum(1 for x in NBs for y in adj[x] if y in NA)
        from itertools import count
        # max matching size via augmenting
        mate = {}
        def aug(x, seen):
            for y in adj[x]:
                if y in NA and y not in seen:
                    seen.add(y)
                    if y not in mate or aug(mate[y], seen):
                        mate[y] = x; return True
            return False
        msz = sum(1 for x in NBs if aug(x, set()))
        print('dist', dd, 'b', b, 'edges N(b)-N(a)', cnt, 'max matching', msz)
