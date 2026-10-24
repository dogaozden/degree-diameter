import sys, itertools
sys.path.insert(0,'/home/user/degree-diameter/research/squads/exp2/r1/c6/scripts')
from hexlib import *
def parse_sol(fn):
    toks = open(fn).read().split()
    i = 0
    assert toks[0] == 'd7hex'; q, N, K, NV = map(int, toks[1:5]); i = 6  # toks[5] = 'freed'
    F = [int(t) for t in toks[i:i+K]]; i += K
    hub = []
    if toks[i] == 'hubedges':
        m = int(toks[i+1]); i += 2
        for e in range(m):
            hub.append((int(toks[i]), int(toks[i+1]))); i += 2
    else:
        m = 0
    M = [int(t) for t in toks[i:i+N]]
    return q, N, K, NV, F, hub, M
if __name__ == '__main__':
    sol = sys.argv[1]
    q, N, LP, PL = load_hex()
    q, N, K, NV, F, hub, M = parse_sol(sol)
    print('K', K, 'NV', NV, 'freed', F, 'hubedges', len(hub))
    Minv = [0]*N
    for p in range(N): Minv[M[p]] = p
    # per freed pair: point coverage set (bitmask over points), line coverage (bitmask over lines)
    covP = []; covL = []
    for j, p in enumerate(F):
        dp = hbfs(N, LP, PL, p, False)           # distances from freed point p
        dl = hbfs(N, LP, PL, M[p], True)         # distances from its line M(p)
        m = 0
        for x in range(N):
            if dp[x] <= 4 or dp[N + M[x]] <= 3:  # route a: ball4 of p ; route b: M(x) within 3 of p
                m |= 1 << x
        covP.append(m)
        ml = 0
        for L in range(N):
            # dual: line L within 4 of M(p) (lines), or point Minv[L] within 3 of M(p)
            if dl[N + L] <= 4 or dl[Minv[L]] <= 3:
                ml |= 1 << L
        covL.append(ml)
    FULL = (1 << N) - 1
    print('single-freed coverage sizes (points):', [bin(c).count('1') for c in covP])
    print('single-freed coverage sizes (lines):', [bin(c).count('1') for c in covL])
    for name, cov in (('points', covP), ('lines', covL)):
        best = None; found = {}
        for s in range(1, K + 1):
            cnt = 0
            for T in itertools.combinations(range(K), s):
                u = 0
                for j in T: u |= cov[j]
                if u == FULL:
                    cnt += 1
                    if cnt <= 3 and s <= 8: found.setdefault(s, []).append(T)
            if cnt: print(name, 'covering subsets of size', s, ':', cnt)
            if cnt and best is None: best = s
        print(name, 'minimum covering subset size:', best, 'examples:', {k: v[:3] for k, v in found.items()})
        if best is None:
            # how far from full: best union size with 7 freed
            bu = 0
            for T in itertools.combinations(range(K), 7):
                u = 0
                for j in T: u |= cov[j]
                bu = max(bu, bin(u).count('1'))
            print(name, 'best 7-subset union:', bu, 'of', N)
