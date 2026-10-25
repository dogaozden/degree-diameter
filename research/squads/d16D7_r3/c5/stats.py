import sys, collections
def load(path):
    with open(path) as f:
        n = int(f.readline())
        W = [0]*n; NB = [None]*n
        for i in range(n):
            a = list(map(int, f.readline().split()))
            W[i] = a[0]; NB[i] = a[2:2+a[1]]
    return W, NB
def loadmap(path):
    return [list(map(int, l.split())) for l in open(path)]
Q = '/home/user/degree-diameter/research/squads/d16D7_r3/quot/'
for name in sys.argv[1:]:
    W, NB = load(Q + name + '.txt')
    n = len(W)
    mp = loadmap(Q + name + '.map')
    sym = all(all(v in set(NB[u]) for u in NB[x]) for x in range(n) for v in [x] if False) # placeholder
    # symmetry check
    S = [set(x) for x in NB]
    asym = sum(1 for x in range(n) for y in NB[x] if x not in S[y])
    selfloop = sum(1 for x in range(n) if x in S[x])
    wc = collections.Counter(W)
    dg = collections.Counter(len(x) for x in NB)
    tot = sum(W)
    msz = collections.Counter(len(m) for m in mp)
    wmatch = all(len(mp[i]) == W[i] for i in range(n))
    degw = collections.defaultdict(list)
    for x in range(n): degw[W[x]].append(len(NB[x]))
    print(name, 'n=%d' % n, 'weights', dict(wc), 'total_orbit_vertices=%d' % tot, 'asym=%d' % asym, 'selfloops=%d' % selfloop,
          'map_sizes_match_weights=%s' % wmatch, 'mindeg/avgdeg/maxdeg per weight', {w: (min(v), round(sum(v)/len(v),1), max(v)) for w, v in degw.items()},
          'edges=%d' % (sum(len(x) for x in NB)//2))
    # orbit-graph vertices covered
    allv = [v for m in mp for v in m]
    print('   map covers', len(allv), 'distinct', len(set(allv)), 'max idx', max(allv))
