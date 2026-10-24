# For a permutation-voltage controller: same-side pairs (c,d) at distance 2 with no label-reduced walk of length 4
# (these are the only pairs a universal chart can miss), listed by the label patterns (t1,t2) of their 2-paths;
# also vertices with no closed label-reduced 4-walk. Sources: one per base vertex.
import sys, collections
T = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
m = len(T); e = next(i for i in range(m) if all(T[i][j] == j for j in range(m)))
inv = [next(j for j in range(m) if T[i][j] == e) for i in range(m)]
c = list(map(int, open(sys.argv[2]).read().split())); k = c[0]; nb = 2 * k
pa = c[2:2+nb]; pb = c[2+nb:2+2*nb]; fa = c[2+2*nb:2+3*nb]; fb = c[2+3*nb:2+4*nb]
pai = [0]*nb; pbi = [0]*nb
for v in range(nb): pai[pa[v]] = v; pbi[pb[v]] = v
def step(t, x):
    v, g = divmod(x, m)
    if t == 0: return pa[v]*m + T[fa[v]][g]
    if t == 1: w = pai[v]; return w*m + T[inv[fa[w]]][g]
    if t == 2: return pb[v]*m + T[fb[v]][g]
    w = pbi[v]; return w*m + T[inv[fb[w]]][g]
L = 'aAbB'
tot = 0; pat = collections.Counter()
for v in range(nb):
    s = v*m + e
    reach4 = set()
    for t1 in range(4):
        x1 = step(t1, s)
        for t2 in range(4):
            if t2 == t1 ^ 1: continue
            x2 = step(t2, x1)
            for t3 in range(4):
                if t3 == t2 ^ 1: continue
                x3 = step(t3, x2)
                for t4 in range(4):
                    if t4 == t3 ^ 1: continue
                    reach4.add(step(t4, x3))
    two = collections.defaultdict(list)
    for t1 in range(4):
        for t2 in range(4):
            if t2 == t1 ^ 1: continue
            two[step(t2, step(t1, s))].append(L[t1] + L[t2])
    defic = [(d, ps) for d, ps in two.items() if d not in reach4]
    if s not in reach4: print(f'base {v}: NO closed reduced 4-walk')
    tot += len(defic)
    for d, ps in defic: pat[tuple(sorted(ps))] += 1
    print(f'base {v}: {len(defic)} deficient distance-2 targets: ' + ' '.join('/'.join(ps) for d, ps in defic))
print('total deficient', tot, 'pattern counts', dict(pat))
