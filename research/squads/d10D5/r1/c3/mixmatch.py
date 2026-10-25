"""mixmatch.py GQBIN SOL0 SEED RESTARTS TRIES: random greedy growth of freed pairs (p, l = sigma(p)) for the
exact-coverage model.  Pair i = (p_i, l_i, g_i, g2_i): g_i a line through p_i (any, for a flag; for a non-flag not the
line through p_i and the projection of p_i onto l_i), g2_i a point on l_i (non-flag: not the projection of p_i).
  G_i = lines meeting g_i at a point != p_i, != g_i   -> sigma^{-1}(M) in perp(p_i) \\ {p_i}, not freed
  Y_i = points collinear with g2_i, not on l_i        -> sigma(Y) in lperp(l_i) \\ {l_i}, not freed
Holes (freed line in some G_i, freed point in some Y_i, self) are forbidden.  Bipartite matching on bitmasks with
warm start from SOL0's sigma (Kuhn augmentation).  env: PF (flag probability), KMAX, OUT (prefix for .sol/.free).
A failed augmentation from a row proves that no perfect matching exists (Berge), so each test is exact."""
import sys, random, os
sys.path.insert(0, '.')
from gq import load

fn, sol0 = sys.argv[1], sys.argv[2]
seed, restarts, tries = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
PF = float(os.environ.get('PF', '0.5')); KMAX = int(os.environ.get('KMAX', '6')); OUT = os.environ.get('OUT', 'k')
q, N, lines, lof = load(fn); Q1 = q + 1; ALL = (1 << N) - 1
onl = [sum(1 << y for y in lines[l]) for l in range(N)]
Pm = [0] * N
for p in range(N):
    s = 0
    for l in lof[p]: s |= onl[l]
    Pm[p] = s
Lm = [0] * N
for l in range(N):
    s = 0
    for p in lines[l]:
        for m in lof[p]: s |= 1 << m
    Lm[l] = s
tok = open(sol0).read().split(); sig0 = list(map(int, tok[7:7 + N])); nu_tok = tok[7 + 4 * N:7 + 4 * N + N * Q1]
assert len(nu_tok) == N * Q1 and sorted(sig0) == list(range(N))

NAT = int(os.environ.get('NAT', '0'))                      # NAT=1: flags only with g = l, g2 = p (flagmatch choice)
def choices(p, l):
    if (onl[l] >> p) & 1:                                   # flag: any g through p, any g2 on l
        if NAT: return [(l, p)]
        return [(g, g2) for g in lof[p] for g2 in lines[l]]
    pi = [y for y in lines[l] if (Pm[p] >> y) & 1][0]      # projection of p onto l
    g0 = [m for m in lof[p] if (onl[m] >> pi) & 1][0]      # line through p and pi
    return [(g, g2) for g in lof[p] if g != g0 for g2 in lines[l] if g2 != pi]

def pair_data(p, l, g, g2):
    G = 0
    for y in lines[g]:
        if y == p: continue
        for m in lof[y]:
            if m != g: G |= 1 << m
    return (p, l, g, g2, G, Pm[p] & ~(1 << p), Pm[g2] & ~onl[l], Lm[l] & ~(1 << l))

def masks_for(pairs, FPm, FLm):
    M = [0] * N
    for x in range(N):
        if (FPm >> x) & 1: continue
        m = ALL & ~FLm
        for (p, l, g, g2, G, Pp, Y, Ll) in pairs:
            if not (Pp >> x) & 1: m &= ~G
            if (Y >> x) & 1: m &= Ll
        M[x] = m
    return M

def augment(M2, mL2, mR2, FPm2):
    fc = [sum(1 << v for v in range(N) if mR2[v] < 0)]
    def dfs(u, vis):
        m = M2[u] & ~vis[0]
        f = m & fc[0]
        if f:
            b = f & -f; v = b.bit_length() - 1; fc[0] ^= b
            mR2[v] = u; mL2[u] = v; return True
        while m:
            b = m & -m; v = b.bit_length() - 1; m ^= b
            if vis[0] & b: continue
            vis[0] |= b
            w = mR2[v]
            if dfs(w, vis):
                mR2[v] = u; mL2[u] = v; return True
            m &= ~vis[0]
        return False
    sys.setrecursionlimit(10000)
    for x in range(N):
        if (FPm2 >> x) & 1 or mL2[x] >= 0: continue
        if not dfs(x, [0]): return False
    return True

def try_add(st, p, l, g, g2):
    pairs, FPm, FLm, mL, mR = st
    pd = pair_data(p, l, g, g2); G, Y = pd[4], pd[6]
    if (1 << l) & G or (1 << p) & Y or (G & FLm) or (Y & FPm): return None
    for pr in pairs:
        if (1 << l) & pr[4] or (1 << p) & pr[6]: return None
    newpairs = pairs + [pd]; FPm2 = FPm | (1 << p); FLm2 = FLm | (1 << l)
    M2 = masks_for(newpairs, FPm2, FLm2)
    mL2 = mL[:]; mR2 = mR[:]
    if mL2[p] >= 0: mR2[mL2[p]] = -1
    if mR2[l] >= 0: mL2[mR2[l]] = -1
    mL2[p] = l; mR2[l] = p
    for x in range(N):
        if (FPm2 >> x) & 1: continue
        v = mL2[x]
        if v >= 0 and not (M2[x] >> v) & 1:
            mR2[v] = -1; mL2[x] = -1
    if not augment(M2, mL2, mR2, FPm2): return None
    return (newpairs, FPm2, FLm2, mL2, mR2)

def write_out(pairs, mL):
    with open(OUT + '.sol', 'w') as f:
        f.write(f'{q} 2 6 7 0\ncyc 6\n'); s = ' '.join(map(str, mL)); f.write(s + '\n' + s + '\n')
        f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(nu_tok) + '\n')
    with open(OUT + '.sol.free', 'w') as f: f.write(' '.join(str(pr[0]) for pr in pairs) + '\n')
    with open(OUT + '.pairs', 'w') as f:
        for pr in pairs: f.write(f'{pr[0]} {pr[1]} {pr[2]} {pr[3]}\n')

best = (-1, None)
for rs in range(restarts):
    rng = random.Random(seed * 1000 + rs)
    mL = sig0[:]; mR = [-1] * N
    for x in range(N): mR[mL[x]] = x
    st = ([], 0, 0, mL, mR); fails = 0
    while fails < tries and len(st[0]) < KMAX:
        p = rng.randrange(N)
        if (st[1] >> p) & 1: fails += 1; continue
        if rng.random() < PF: l = rng.choice(lof[p])
        else: l = rng.choice([l for l in range(N) if not (onl[l] >> p) & 1 and not (st[2] >> l) & 1])
        if (st[2] >> l) & 1: fails += 1; continue
        g, g2 = rng.choice(choices(p, l))
        res = try_add(st, p, l, g, g2)
        if res is None: fails += 1; continue
        st = res; fails = 0
        nfl = sum(1 for pr in st[0] if (onl[pr[1]] >> pr[0]) & 1)
        print('k', len(st[0]), 'flags', nfl, 'nonflag', len(st[0]) - nfl, flush=True)
    k = len(st[0])
    print('RESTART', rs, 'k', k, flush=True)
    if k > best[0]: best = (k, st)
    if k >= KMAX: break
k, st = best
print('BEST k', k, 'pairs', ' '.join(f'{pr[0]}:{pr[1]}:g{pr[2]}:h{pr[3]}:{"F" if (onl[pr[1]] >> pr[0]) & 1 else "N"}' for pr in st[0]))
if k >= 1:
    write_out(st[0], st[3]); print('WROTE', OUT + '.sol', flush=True)
