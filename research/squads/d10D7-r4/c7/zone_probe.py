import numpy as np, random, struct, sys
fn = '/home/user/degree-diameter/research/d10D7/hex/hex_q5.bin'
with open(fn, 'rb') as f:
    q, N, NL = struct.unpack('<iii', f.read(12))
    LP = np.frombuffer(f.read(4 * N * (q + 1)), dtype=np.int32).reshape(N, q + 1)
Q1 = q + 1
PL = [[] for _ in range(N)]
for l in range(N):
    for p in LP[l]:
        PL[p].append(l)
PL = np.array(PL)
def pdist(x):
    # incidence distances from point x to all points (even values), via BFS on points-lines
    dp = -np.ones(N, dtype=int); dl = -np.ones(N, dtype=int)
    dp[x] = 0; frontier_p = [x]; d = 0
    while frontier_p:
        nl = []
        for p in frontier_p:
            for l in PL[p]:
                if dl[l] < 0:
                    dl[l] = d + 1; nl.append(l)
        np_ = []
        for l in nl:
            for p in LP[l]:
                if dp[p] < 0:
                    dp[p] = d + 2; np_.append(p)
        frontier_p = np_; d += 2
    return dp
random.seed(1)
Z = {}
def zone(x):
    if x not in Z:
        dp = pdist(x)
        Z[x] = set(np.nonzero((dp >= 0) & (dp <= 4))[0].tolist())
    return Z[x]
print('zone size (B0+B2+B4) =', len(zone(0)), ' B2 =', int(np.sum(pdist(0) == 2)))
res = {}
for trial in range(6):
    w = random.randrange(N)
    lines = PL[w]
    pts = []
    for L in lines:
        cands = [x for x in LP[L] if x != w]
        pts.append(random.choice(cands))
    for a in [1, 2, 3, 6]:
        U = set()
        for p in pts[:a]:
            U |= zone(p)
        res.setdefault(a, []).append(len(U))
for a in sorted(res):
    v = res[a]
    print('star size', a, 'union zone', min(v), '..', max(v), ' per pair ~', round(sum(v) / len(v) / a, 1))
