import sys
from collections import Counter
Q = '/home/user/degree-diameter/research/squads/d16D7_r3/quot/'
R2 = '/home/user/degree-diameter/research/squads/d16D7_r2/'
for kind in ['pts', 'lines']:
    with open(Q + 'qh_%s.txt' % kind) as f:
        n = int(f.readline())
        W = []; NB = []
        for i in range(n):
            a = list(map(int, f.readline().split()))
            W.append(a[0]); NB.append(a[2:2 + a[1]])
    # symmetry check
    S = [set(x) for x in NB]
    asym = sum(1 for i in range(n) for j in NB[i] if i not in S[j])
    selfl = sum(1 for i in range(n) if i in S[i])
    mp = [list(map(int, l.split())) for l in open(Q + 'qh_%s.map' % kind)]
    mw = [len(m) for m in mp]
    assert mw == W, 'map sizes differ from weights'
    tot = sum(W)
    cnt = Counter(W)
    degs = [len(x) for x in NB]
    print(kind, 'n', n, 'weights', dict(cnt), 'total weight', tot, 'asym', asym, 'self', selfl,
          'deg min/avg/max', min(degs), round(sum(degs)/n, 1), max(degs))
    # orbit-graph vertex -> quotient vertex
    og = {}
    M = None
    with open(R2 + 'og_%s.txt' % kind) as f:
        M, E = map(int, f.readline().split())
    qid = [-1] * M
    for i, m in enumerate(mp):
        for v in m:
            assert qid[v] == -1
            qid[v] = i
    print('  orbit graph M', M, 'covered', sum(1 for x in qid if x >= 0), 'uncovered (dropped orbits)', sum(1 for x in qid if x < 0))
    # seed check
    seed = [int(x) for x in open(Q + '../seed_%s.txt' % kind).read().split() if x.strip()]
    qs = sorted(set(qid[v] for v in seed))
    ok = all(qid[v] >= 0 for v in seed)
    print('  seed size', len(seed), 'maps into quotient vertices', len(qs), 'all covered', ok,
          'quotient weight of seed image', sum(W[i] for i in qs))
    # is the seed image a union of whole quotient vertices, and independent in the quotient?
    sq = set(qs)
    indep = all(not (S[i] & sq) for i in qs)
    print('  seed image independent in quotient', indep, ' full-cover', all(set(mp[i]) <= set(seed) for i in qs))
