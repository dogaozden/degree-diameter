# Independent check (Python): for random block removals on the orbit graph, rebuild the free set C, split it into
# components and compare the removed count with the exact alpha (bitmask recursion) of each small component.
# Also counts maximum independent sets (alternatives) to see whether the removed set is unique.
import random, sys
from functools import lru_cache
R2 = '/home/user/degree-diameter/research/squads/d16D7_r2/'
R3 = '/home/user/degree-diameter/research/squads/d16D7_r3/'
g = sys.argv[1]
ntr = int(sys.argv[2]) if len(sys.argv) > 2 else 30
M = None
with open(R2 + 'og_%s.txt' % g) as f:
    M, E = map(int, f.readline().split())
    adj = [None] * M
    for line in f:
        a = list(map(int, line.split()))
        adj[a[0]] = a[3:3 + a[2]]
S0 = set(int(x) for x in open(R3 + 'seed_%s.txt' % g) if x.strip())
blocks = [list(map(int, l.split())) for l in open(R3 + 'quot/q9_%s.map' % g)]
cov = set(v for b in blocks for v in b)
blocks += [[v] for v in range(M) if v not in cov]
blk_of = {}
for i, b in enumerate(blocks):
    for v in b:
        blk_of[v] = i
Sblocks = sorted(set(blk_of[v] for v in S0))
random.seed(5)

def count_max_is(verts, nbr):
    # returns (alpha, number of maximum independent sets) for graph on verts (list), nbr dict restricted
    idx = {v: i for i, v in enumerate(verts)}
    n = len(verts)
    nb = [0] * n
    for v in verts:
        for u in adj[v]:
            if u in idx:
                nb[idx[v]] |= 1 << idx[u]
    best = [0, 0]  # alpha, count
    def rec(P, size):
        # P bitmask of candidates
        if P == 0:
            if size > best[0]:
                best[0], best[1] = size, 1
            elif size == best[0]:
                best[1] += 1
            return
        # bound
        if size + bin(P).count('1') < best[0]:
            return
        # pick lowest vertex with max degree
        v = (P & -P).bit_length() - 1
        rec(P & ~nb[v] & ~(1 << v), size + 1)   # include v
        rec(P & ~(1 << v), size)                # exclude v
    rec((1 << n) - 1, 0)
    return best[0], best[1]

stats = dict(comps=0, big=0, bigger=0, tied_unique=0, tied_multi=0)
for t in range(ntr):
    k = random.randint(3, 10)
    ch = random.sample(Sblocks, k)
    rem = set(v for b in ch for v in blocks[b] if v in S0)
    S2 = S0 - rem
    conf = {}
    for v in S2:
        for u in adj[v]:
            conf[u] = conf.get(u, 0) + 1
    C = [v for v in range(M) if v not in S2 and conf.get(v, 0) == 0]
    Cset = set(C)
    seen = set()
    for s in C:
        if s in seen:
            continue
        comp = []
        stack = [s]; seen.add(s)
        while stack:
            x = stack.pop(); comp.append(x)
            for u in adj[x]:
                if u in Cset and u not in seen:
                    seen.add(u); stack.append(u)
        rc = sum(1 for v in comp if v in rem)
        stats['comps'] += 1
        if len(comp) > 40:
            stats['big'] += 1
            continue
        alpha, cnt = count_max_is(comp, None)
        if alpha > rc:
            stats['bigger'] += 1
            print('IMPROVING COMPONENT found: alpha %d > removed %d' % (alpha, rc))
        elif cnt == 1:
            stats['tied_unique'] += 1
        else:
            stats['tied_multi'] += 1
print(g, stats)
