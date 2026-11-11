# number of distinct signed dart-count vectors (abelian voltage functionals) among NB walks r -> w of length <= 8 (even) / <= 9 (odd)
import collections
L_ = open('w3base.txt').read().split()
n, m = int(L_[0]), int(L_[1])
E = [(int(L_[2+2*i]), int(L_[3+2*i])) for i in range(m)]
eid = {}
for i, (u, v) in enumerate(E): eid[(u, v)] = (i, 1); eid[(v, u)] = (i, -1)
adj = collections.defaultdict(list)
for u, v in E: adj[u].append(v); adj[v].append(u)
def walks(root, Lmax):
    out = collections.defaultdict(list)   # target -> list of (length, signed vector as tuple of (edge, sign) sums)
    stack = [(root, -1, 0, ())]
    while stack:
        x, p, L, darts = stack.pop()
        if L > 0: out[x].append((L, darts))
        if L == Lmax: continue
        for y in adj[x]:
            if y != p:
                stack.append((y, x, L + 1, darts + (eid[(x, y)],)))
    return out
for root in [0, 40]:
    W = walks(root, 9)
    stats = []
    for w in range(80):
        if (w < 40) != (root < 40): continue
        vecs = collections.Counter()
        for L, darts in W[w]:
            if L % 2 == 0 and L <= 8:
                v = collections.Counter()
                for (i, s) in darts: v[i] += s
                vecs[tuple(sorted((k, c) for k, c in v.items() if c))] += 1
        stats.append((len(vecs), sum(vecs.values())))
    print('root', root, 'same-side targets (distinct signed vectors, walks):', sorted(set(stats))[:5], '...')
