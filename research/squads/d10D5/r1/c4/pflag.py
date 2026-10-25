"""pflag.py: bitset perfect-matching model of flaggreedy.py (copied) + hub-graph requirements (patch edges and
common-neighbour pairs) + annealing for a degree-capped hub-hub bipartite graph B.
Hub indexing (as dmhub.c / build_hub.py): line-class hub of freed flag x, twin s: a = x*H + s (joined to fibre p_x);
point-class hub of flag y, twin t: b = y*H + t (joined to fibre l_y).  B[a][b] = 1 means a hub-hub edge.
Requirements (x != y):
  PATCH  R(x,y) = NEED1[x][y] or NEED2[y][x]: some twin pair of (L_x, P_y) is an edge.
         NEED1[x][y]: l_y meets l_x at a point other than p_x (hole of p_x at the points of l_y).
         NEED2[y][x]: p_x collinear with p_y, not on l_y (hole of l_y at the lines through p_x).
  COMMON if p_x, p_y not collinear: every twin pair of L-hubs has a common P-hub neighbour.
  COMMON if l_x, l_y not concurrent: every twin pair of P-hubs has a common L-hub neighour.
Each hub has at most SPARE = 4 hub-hub edges (degree 6 + 4 = 10)."""
import sys, random
sys.path.insert(0, '.')
from gq import load

q, N, lines, lof = load('gq/gq_q7.bin')
Q1 = q + 1
Pm = [0] * N; Lm = [0] * N; onl = [0] * N; thr = [0] * N
for p in range(N):
    s = 0
    for l in lof[p]: 
        for y in lines[l]: s |= 1 << y
    Pm[p] = s; thr[p] = sum(1 << m for m in lof[p])
for l in range(N):
    onl[l] = sum(1 << y for y in lines[l])
    s = 0
    for p in lines[l]:
        for m in lof[p]: s |= 1 << m
    Lm[l] = s
ALL = (1 << N) - 1
H = 2; SPARE = 4

def matching(flags):
    F = {p: l for p, l in flags}; Fl = {l for p, l in flags}
    Fm = sum(1 << p for p in F); Flm = sum(1 << l for l in Fl)
    lineok = [ALL & ~Flm] * N
    ptok = [ALL & ~Fm] * N
    for p, l in flags:
        A = Pm[p] & ~onl[l]; G = Lm[l] & ~thr[p]
        Ll = Lm[l] & ~(1 << l); Pp = Pm[p] & ~(1 << p)
        x = A
        while x:
            b = x & -x; i = b.bit_length() - 1; lineok[i] &= Ll; x ^= b
        m = G
        while m:
            b = m & -m; i = b.bit_length() - 1; ptok[i] &= Pp; m ^= b
    adj = []
    for x in range(N):
        if x in F: adj.append([F[x]]); continue
        row = []; m = lineok[x]
        while m:
            b = m & -m; M = b.bit_length() - 1; m ^= b
            if ptok[M] >> x & 1: row.append(M)
        adj.append(row)
    matchR = [-1] * N; matchL = [-1] * N
    for x in F:
        M = F[x]; matchR[M] = x; matchL[x] = M
    sys.setrecursionlimit(20000)
    def aug(u, seen):
        for v in adj[u]:
            if v in seen: continue
            seen.add(v)
            if matchR[v] < 0 or aug(matchR[v], seen):
                matchR[v] = u; matchL[u] = v; return True
        return False
    for u in range(N):
        if matchL[u] < 0: aug(u, set())
    return sum(1 for u in range(N) if matchL[u] >= 0), matchL

def relations(flags):
    k = len(flags)
    NEED1 = [[False] * k for _ in range(k)]; NEED2 = [[False] * k for _ in range(k)]
    coll = [[False] * k for _ in range(k)]; conc = [[False] * k for _ in range(k)]
    for i, (p, l) in enumerate(flags):
        for j, (r, m) in enumerate(flags):
            if i == j: continue
            coll[i][j] = bool(Pm[p] >> r & 1)
            conc[i][j] = bool(Lm[l] >> m & 1)
            NEED1[i][j] = bool(Lm[l] >> m & 1) and not (thr[p] >> m & 1)
            NEED2[i][j] = bool(Pm[p] >> r & 1) and not (onl[l] >> r & 1)
    # patch requirement on edge (L_x, P_y)
    patch = [[False] * k for _ in range(k)]
    for x in range(k):
        for y in range(k):
            if x != y: patch[x][y] = NEED1[x][y] or NEED2[y][x]
    commA = [(x, y) for x in range(k) for y in range(k) if x < y and not coll[x][y]]
    commB = [(x, y) for x in range(k) for y in range(k) if x < y and not conc[x][y]]
    return patch, commA, commB, coll, conc, NEED1, NEED2

def hub_anneal(k, patch, commA, commB, iters=200000, seed=1, T0=1.0, T1=0.02):
    """Find B (K x K, K = H*k, row = L-hub, col = P-hub) with row/col sums <= SPARE meeting all requirements.
    Returns (cost, B) with cost = number of violated requirements (0 = feasible)."""
    rng = random.Random(seed)
    K = H * k
    B = [[0] * K for _ in range(K)]
    rdeg = [0] * K; cdeg = [0] * K
    pat_req = [(x, y) for x in range(k) for y in range(k) if patch[x][y]]
    def cost():
        c = 0
        for x, y in pat_req:
            if not any(B[x * H + s][y * H + t] for s in range(H) for t in range(H)): c += 1
        for x, y in commA:
            for s in range(H):
                for t in range(H):
                    a, a2 = x * H + s, y * H + t
                    if not any(B[a][b] and B[a2][b] for b in range(K)): c += 1
        for x, y in commB:
            for s in range(H):
                for t in range(H):
                    b, b2 = x * H + s, y * H + t
                    if not any(B[a][b] and B[a][b2] for a in range(K)): c += 1
        return c
    c = cost(); best = c; bestB = [r[:] for r in B]
    for it in range(iters):
        if c == 0: break
        T = T0 * (T1 / T0) ** (it / iters)
        a = rng.randrange(K); b = rng.randrange(K)
        if B[a][b]:
            B[a][b] = 0; rdeg[a] -= 1; cdeg[b] -= 1
            c2 = cost()
            if c2 <= c or rng.random() < pow(2.718281828, -(c2 - c) / T): c = c2
            else: B[a][b] = 1; rdeg[a] += 1; cdeg[b] += 1
        else:
            added = []
            if rdeg[a] >= SPARE:   # drop a random edge of row a
                cand = [bb for bb in range(K) if B[a][bb]]; bb = rng.choice(cand)
                B[a][bb] = 0; rdeg[a] -= 1; cdeg[bb] -= 1; added.append((a, bb))
            if cdeg[b] >= SPARE:
                cand = [aa for aa in range(K) if B[aa][b]]; aa = rng.choice(cand)
                B[aa][b] = 0; rdeg[aa] -= 1; cdeg[b] -= 1; added.append((aa, b))
            B[a][b] = 1; rdeg[a] += 1; cdeg[b] += 1
            c2 = cost()
            if c2 <= c or rng.random() < pow(2.718281828, -(c2 - c) / T): c = c2
            else:
                B[a][b] = 0; rdeg[a] -= 1; cdeg[b] -= 1
                for (aa, bb) in added: B[aa][bb] = 1; rdeg[aa] += 1; cdeg[bb] += 1
        if c < best: best = c; bestB = [r[:] for r in B]
    return best, bestB
