# g15 check: G = SL(2,p) x Z_n, alpha = conj by M (order 3) x (z -> r z), f = 0 (S = free alpha-orbits).
# Ground truth: BFS on the Haar graph H(G,S). Checks: (1) d_A invariant under alpha and inversion,
# (2) sequences of h blocks with product -I: counts mod 3 and mod 2, orbit closure under D_h x Z_3,
# (3) empirical P(-I uncovered on side A) vs exp(-lambda/(6h)), lambda = Delta^(2h)/N.
import itertools, random, sys, math
p, n, r = 5, 7, 2
M = (0, p-1, 1, p-1)            # [[0,-1],[1,-1]], order 3, det 1
Mi = (p-1, p-1, 1, 0)           # inverse: [[-1,-1],[1,0]] ... check below
def mm(X, Y):
    a,b,c,d = X; e,f,g,h = Y
    return ((a*e+b*g)%p, (a*f+b*h)%p, (c*e+d*g)%p, (c*f+d*h)%p)
def inv2(X):
    a,b,c,d = X; return (d%p, (-b)%p, (-c)%p, a%p)
assert mm(M, inv2(M)) == (1,0,0,1)
Minv = inv2(M)
els = []
for a,b,c,d in itertools.product(range(p), repeat=4):
    if (a*d-b*c) % p == 1:
        for z in range(n):
            els.append(((a,b,c,d), z))
idx = {g: i for i, g in enumerate(els)}
N = len(els)
def mul(x, y): return (mm(x[0], y[0]), (x[1]+y[1]) % n)
def inv(x): return (inv2(x[0]), (-x[1]) % n)
def alpha(x):
    return (mm(mm(M, x[0]), Minv), (r*x[1]) % n)
e = ((1,0,0,1), 0)
mI = ((p-1,0,0,p-1), 0)   # -I
assert idx[e] is not None
A_al = [idx[alpha(g)] for g in els]
A_inv = [idx[inv(g)] for g in els]
MUL = None
def bfs(S):
    # Haar graph: (g,A)~(s g,B). vertices A: 0..N-1, B: N..2N-1
    adj = [[] for _ in range(2*N)]
    for gi, g in enumerate(els):
        for s in S:
            hi = idx[mul(s, g)]
            adj[gi].append(N+hi); adj[N+hi].append(gi)
    dist = [[-1]*(2*N) for _ in range(2)]
    for side in range(2):
        start = (0 if side == 0 else N) + idx[e]
        d = dist[side]; d[start] = 0; q = [start]
        for u in q:
            for v in adj[u]:
                if d[v] < 0: d[v] = d[u]+1; q.append(v)
    return dist
def random_S(m, rng):
    while True:
        S = []
        used = set()
        ok = True
        for _ in range(m):
            x = els[rng.randrange(N)]
            orb = [x, alpha(x), alpha(alpha(x))]
            ids = {idx[o] for o in orb}
            if len(ids) < 3 or ids & used or idx[e] in ids:
                ok = False; break
            used |= ids; S += orb
        if ok: return S
def seqs_product_mI(S, h):
    # blocks a = s^-1 t for pairs (s,t) in S x S; count sequences of h pairs with product -I
    pairs = [(s, t) for s in S for t in S]
    blk = {}
    for (s,t) in pairs:
        blk.setdefault(None, [])
    cnt = 0
    tot = 0
    bl = [mul(inv(s), t) for (s,t) in pairs]
    # DP over products: dict product-index -> count
    dp = {idx[e]: 1}
    for _ in range(h):
        nd = {}
        for g, c in dp.items():
            for b in bl:
                k = idx[mul(els[g], b)]
                nd[k] = nd.get(k, 0) + c
        dp = nd
    return dp.get(idx[mI], 0), dp
if __name__ == "__main__":
    h = int(sys.argv[1]); m = int(sys.argv[2]); trials = int(sys.argv[3]); seed = int(sys.argv[4])
    D = 2*h+1
    rng = random.Random(seed)
    nmiss = 0; bad_inv = 0; bad_alpha = 0; mod3 = 0; cnts = []
    for t in range(trials):
        S = random_S(m, rng)
        dist = bfs(S)
        dA = dist[0]
        # (1) invariance of side-A distances under alpha and inversion
        for gi in range(N):
            if dA[gi] != dA[A_al[gi]]: bad_alpha += 1
            if dA[gi] != dA[A_inv[gi]]: bad_inv += 1
        c, dp = seqs_product_mI(S, h)
        cnts.append(c)
        if c % 6: mod3 += 1
        if dA[idx[mI]] == -1 or dA[idx[mI]] > 2*h:
            nmiss += 1
    lam = (len(S)**(2*h)) / N
    print(f"h={h} D={D} Delta={3*m} N={N} lambda={lam:.3f} trials={trials}")
    print(f"alpha-invariance violations={bad_alpha} inversion violations={bad_inv}")
    print(f"sequences with product -I: count mod 6 nonzero in {mod3}/{trials} trials (expect 0)")
    print(f"-I uncovered on side A (BFS): {nmiss}/{trials} = {nmiss/trials:.3f}; exp(-lambda/(6h)) = {math.exp(-lam/(6*h)):.3f}; exp(-lambda)={math.exp(-lam):.3f}")
    print("counts of -I sequences (first 20):", cnts[:20])
