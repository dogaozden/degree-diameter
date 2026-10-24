import sys, collections, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c4')
from c4lib import Torus
T = Torus(5)
n = T.nT
idx = {(d[0], d[1]): i for i, d in enumerate(T.T)}
def mul(i, j):
    a = T.T[i]; b = T.T[j]
    return idx[((a[0]*b[0]) % 5, (a[1]*b[1]) % 5)]
def closure(gens):
    S = {0}
    frontier = [0]
    while frontier:
        x = frontier.pop()
        for g in gens:
            y = mul(x, g)
            if y not in S:
                S.add(y); frontier.append(y)
    return frozenset(S)
subs = set()
for r in (1, 2):
    for gens in itertools.combinations(range(n), r):
        subs.add(closure(gens))
subs = sorted(subs, key=lambda K: (len(K), sorted(K)))
print('number of subgroups', len(subs), 'orders', collections.Counter(len(K) for K in subs))
def orbit_types(K, stabs, nobj):
    # K-orbits on objects; type = Stab_K(x)
    seen = [False]*nobj
    cnt = collections.Counter()
    for x in range(nobj):
        if not seen[x]:
            # orbit under K
            orb = set()
            for t in K:
                orb.add(None)
            Ox = sorted(set(int(T_perm[t][x]) for t in K))
            for y in Ox: seen[y] = True
            S = frozenset(t for t in K if T_perm[t][x] == x)
            cnt[S] += 1
    return cnt
T_perm = T.pperm
L_perm = T.lperm
res = []
for K in subs:
    if len(K) == 1: continue
    global_ok = True
    # points
    T_perm = T.pperm; cp = orbit_types(K, None, T.N)
    T_perm = T.lperm; cl = orbit_types(K, None, T.N)
    ok = (cp == cl)
    res.append((len(K), ok, sorted(K), sum(cp.values()), sum(cl.values())))
for r in res:
    if r[1]:
        print('MATCH order', r[0], 'K', r[2], 'orbits pts', r[3], 'lines', r[4])
print('non-matching orders:', collections.Counter(r[0] for r in res if not r[1]))
print('matching orders:', collections.Counter(r[0] for r in res if r[1]))
