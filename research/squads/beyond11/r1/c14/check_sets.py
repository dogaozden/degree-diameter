# c14: brute-force check of the odd-D Haar-graph criterion on tiny groups.
# Haar graph H(G,S): vertices (g,A)=g, (g,B)=|G|+g; edges (g,A) ~ (s g, B), s in S.
# Claim (odd D=2t+1, e in S): diam <= D  iff  (S^-1 S)^t = G  and  (S S^-1)^t = G.
import itertools, sys
from collections import deque

def closure_group(gens, mul, e):
    elems = {e}; frontier = [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(x, g)
                if y not in elems:
                    elems.add(y); nxt.append(y)
        frontier = nxt
    return sorted(elems, key=repr)

def perm_mul(p, q):   # (p*q)(i) = p(q(i))
    return tuple(p[i] for i in q)

def sl23_mul(A, B):
    a, b, c, d = A; e_, f, g, h = B
    return ((a*e_ + b*g) % 3, (a*f + b*h) % 3, (c*e_ + d*g) % 3, (c*f + d*h) % 3)

def quat_mul(x, y):   # x,y = (sign, unit) with unit in '1ijk'
    sx, ux = x; sy, uy = y
    table = {('1','1'):(1,'1'),('1','i'):(1,'i'),('1','j'):(1,'j'),('1','k'):(1,'k'),
             ('i','1'):(1,'i'),('i','i'):(-1,'1'),('i','j'):(1,'k'),('i','k'):(-1,'j'),
             ('j','1'):(1,'j'),('j','i'):(-1,'k'),('j','j'):(-1,'1'),('j','k'):(1,'i'),
             ('k','1'):(1,'k'),('k','i'):(1,'j'),('k','j'):(-1,'i'),('k','k'):(-1,'1')}
    s, u = table[(ux, uy)]
    return (sx*sy*s, u)

def build_groups():
    groups = {}
    # S3 on 3 points
    groups['S3'] = closure_group([(1,0,2),(1,2,0)], perm_mul, (0,1,2))
    # D4 (order 8) on 4 points
    groups['D4'] = closure_group([(1,2,3,0),(0,3,2,1)], perm_mul, (0,1,2,3))
    # A4 on 4 points
    groups['A4'] = closure_group([(1,2,0,3),(1,0,3,2)], perm_mul, (0,1,2,3))
    # Q8
    groups['Q8'] = closure_group([(1,'i'),(1,'j')], quat_mul, (1,'1'))
    # SL(2,3)
    groups['SL23'] = closure_group([(1,1,0,1),(0,2,1,0),(1,0,0,1)], sl23_mul, (1,0,0,1))
    return groups

def tables(G):
    idx = {g: i for i, g in enumerate(G)}
    n = len(G)
    op = {}
    return idx

def analyse(name, G, mul):
    n = len(G)
    idx = {g: i for i, g in enumerate(G)}
    e = G[0] if False else None
    M = [[idx[mul(a, b)] for b in G] for a in G]
    ident = [i for i in range(n) if all(M[i][j] == j for j in range(n))][0]
    inv = [next(j for j in range(n) if M[i][j] == ident) for i in range(n)]
    def setmul(X, Y):
        return {M[x][y] for x in X for y in Y}
    def power(X, t):
        R = {ident}
        for _ in range(t):
            R = setmul(R, X)
        return R
    def diam(S):
        # Haar graph BFS, returns diameter (inf if disconnected)
        N = 2 * n
        adj = [[] for _ in range(N)]
        for g in range(n):
            for s in S:
                h = M[s][g]
                adj[g].append(n + h); adj[n + h].append(g)
        best = 0
        for v in range(N):
            dist = [-1] * N; dist[v] = 0; dq = deque([v])
            while dq:
                x = dq.popleft()
                for y in adj[x]:
                    if dist[y] < 0:
                        dist[y] = dist[x] + 1; dq.append(y)
            if min(dist) < 0:
                return float('inf')
            best = max(best, max(dist))
        return best
    results = []
    all_sets = []
    for k in range(2, 5):
        for rest in itertools.combinations([i for i in range(n) if i != ident], k - 1):
            S = (ident,) + rest
            all_sets.append(S)
    counts = {'agree': 0, 'disagree': 0, 'one_side_only': []}
    for S in all_sets:
        Sset = set(S)
        P1 = setmul({inv[s] for s in S}, Sset)   # S^-1 S
        P2 = setmul(Sset, {inv[s] for s in S})   # S S^-1
        d = diam(S)
        for t in (1, 2):
            c1 = len(power(P1, t)) == n
            c2 = len(power(P2, t)) == n
            pred = c1 and c2
            actual = (d <= 2 * t + 1)
            if pred == actual:
                counts['agree'] += 1
            else:
                counts['disagree'] += 1
            if c1 != c2 and len(counts['one_side_only']) < 6:
                counts['one_side_only'].append((t, S, [G[i] for i in S], 'S^-1S covers' if c1 else 'SS^-1 covers', d))
    return len(all_sets), counts

if __name__ == '__main__':
    groups = build_groups()
    mults = {'S3': perm_mul, 'D4': perm_mul, 'A4': perm_mul, 'Q8': quat_mul, 'SL23': sl23_mul}
    for name in ['S3', 'D4', 'A4', 'Q8', 'SL23']:
        G = groups[name]
        nsets, counts = analyse(name, G, mults[name])
        print(name, 'order', len(G), 'subsets tried', nsets, 'iff agree', counts['agree'],
              'disagree', counts['disagree'])
        for row in counts['one_side_only'][:4]:
            print('   one-side-only:', row)
        sys.stdout.flush()
