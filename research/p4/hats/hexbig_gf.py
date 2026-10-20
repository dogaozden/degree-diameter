"""Field-generic version of hexbig.py (any odd prime power q, e.g. 9), using lib.GF tables.

Exact whisker sets on H(q), with the symmetric reduction found at q = 3, 5, 7.

H(q): points of X0X4 + X1X5 + X2X6 = X3^2 in PG(6,q); the lines through x are the lines through x in the plane
pi_x = {y : Tits' six equations and B(x,y) = 0} (linear in y). Same model and numbering conventions as
research/gh6/gh_build.py (but points are numbered by sorted base-q code, so indices differ).
v = <e1, e6>; S = lines in the hyperplane X0 + c X4 = 0 (-c a non-square); root elements from g2_gens.py patterns
with the generic coefficients; K_S = {x1(a) x2(b) x3(s) x4(c b) x5(-2a/c)}; K = a subgroup of order q^2 (centre
x3(s) and one direction) fixing a good set E of q blocks through v; torus diag(1,g,1/g,1,1,1/g,g).
Then the orbit ILP; writes whiskers_big_q{q}.json and (with 'build') the graph as text for ./diam.

python3 hexbig.py q SECONDS [build]
"""
import itertools
import json
import subprocess
import sys
import time
from collections import Counter, deque
from pathlib import Path

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix

HERE = Path(__file__).resolve().parent
q, secs = int(sys.argv[1]), float(sys.argv[2])
build = len(sys.argv) > 3 and sys.argv[3] == 'build'
ARITY = next((int(a.split('=')[1]) for a in sys.argv if a.startswith('--arity=')), 2)
LOAD = '--load' in sys.argv
t0 = time.time()
sys.path.insert(0, str(HERE.parents[2] / 'problems' / 'bipartite_dd'))
import lib  # noqa: E402
F = lib.GF(q)
ADD, MUL, NEG = F.add_table, F.mul_table, F._neg
INV = np.zeros(q, dtype=np.int64)
for x in range(1, q):
    INV[x] = next(y for y in range(1, q) if MUL[x, y] == 1)
inv = INV.tolist()
POW = q ** np.arange(7, dtype=np.int64)
GEN = int(F._primitive)


def fsum(arrs):
    out = arrs[0]
    for a in arrs[1:]:
        out = ADD[out, a]
    return out


def fmatvec_rows(V, M):
    """rows of V times M^T over GF(q): out[:, j] = sum_k V[:, k] M[j, k]"""
    return np.stack([fsum([MUL[V[:, k], M[j, k]] for k in range(7)]) for j in range(7)], axis=1)


def fmatmul(A, B):
    return np.array([[fsum([MUL[A[i, k], B[k, j]] for k in range(7)]) for j in range(7)] for i in range(7)])


def log(*a):
    print(f'[{time.time()-t0:6.0f}s]', *a, flush=True)


def normalize(V):
    """Rows of V (int64, mod q) scaled so the first nonzero entry is 1."""
    nz = V != 0
    first = np.argmax(nz, axis=1)
    lead = V[np.arange(len(V)), first]
    return MUL[V, INV[lead][:, None]]


# points
pts = []
for f in range(7):
    k = 6 - f
    if k:
        grid = np.array(list(itertools.product(range(q), repeat=k)), dtype=np.int64)
    else:
        grid = np.zeros((1, 0), dtype=np.int64)
    V = np.zeros((len(grid), 7), dtype=np.int64)
    V[:, f] = 1
    V[:, f + 1:] = grid
    Qv = fsum([MUL[V[:, 0], V[:, 4]], MUL[V[:, 1], V[:, 5]], MUL[V[:, 2], V[:, 6]], NEG[MUL[V[:, 3], V[:, 3]]]])
    pts.append(V[Qv == 0])
P = np.concatenate(pts)
codes = P @ POW
order = np.argsort(codes)
P, codes = P[order], codes[order]
N = len(P)
assert N == (q ** 6 - 1) // (q - 1), N
log('points', N)


def index_of(V):
    c = normalize(V) @ POW
    i = np.searchsorted(codes, c)
    assert np.all(codes[np.minimum(i, N - 1)] == c), 'not a point'
    return i


# the plane pi_x for every x: rows of the 7x7 system M_x y = 0
PAIRS = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)), ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]


def system(x):
    M = np.zeros((7, 7), dtype=np.int64)
    for r, ((i, j), (k, l)) in enumerate(PAIRS):  # p_ij - p_kl = 0, p_ij = x_i y_j - x_j y_i
        M[r, j] = ADD[M[r, j], x[i]]; M[r, i] = ADD[M[r, i], NEG[x[j]]]
        M[r, l] = ADD[M[r, l], NEG[x[k]]]; M[r, k] = ADD[M[r, k], x[l]]
    # polar form B(x,y) = x0y4 + x4y0 + x1y5 + x5y1 + x2y6 + x6y2 - 2x3y3
    M[6] = [x[4], x[5], x[6], NEG[ADD[x[3], x[3]]], x[0], x[1], x[2]]
    return M


def nullspace(M):
    M = M.copy()
    rows, piv = 0, []
    for col in range(7):
        r = next((r for r in range(rows, 7) if M[r, col]), None)
        if r is None:
            continue
        M[[rows, r]] = M[[r, rows]]
        M[rows] = MUL[M[rows], inv[M[rows, col]]]
        for r2 in range(7):
            if r2 != rows and M[r2, col]:
                M[r2] = ADD[M[r2], NEG[MUL[M[r2, col], M[rows]]]]
        piv.append(col)
        rows += 1
    free = [c for c in range(7) if c not in piv]
    basis = []
    for fcol in free:
        y = np.zeros(7, dtype=np.int64)
        y[fcol] = 1
        for r, pc in enumerate(piv):
            y[pc] = NEG[M[r, fcol]]
        basis.append(y)
    return basis


line_pts = []
S_all = np.arange(q)
for xi in range(N):
    x = P[xi]
    B = nullspace(system(x))
    assert len(B) == 3, (xi, len(B))
    # choose u, w in the plane with <x, u, w> = the plane (rank 3 mod q)
    cand = list(B)
    best = None
    for u, w in itertools.combinations(cand, 2):
        Mx = np.array([x, u, w])
        if len(nullspace(np.vstack([Mx, np.zeros((4, 7), dtype=np.int64)]).T.copy())) == 4:
            best = (u, w)
            break
    if best is None:
        raise SystemExit(f'no complement at point {xi}')
    u, w = best
    dirs = [ADD[u, MUL[t, w]] for t in range(q)] + [w]
    for y in dirs:
        V = np.vstack([ADD[y[None, :], MUL[S_all[:, None], x[None, :]]], x[None, :]])
        idx = index_of(V)
        if idx.min() == xi:
            line_pts.append(np.sort(idx))
    if xi % 20000 == 0:
        log('point', xi, 'lines so far', len(line_pts))
lines = np.array(line_pts)
assert len(lines) == N, len(lines)
log('lines', len(lines))
if '--checkbase' in sys.argv:  # the incidence graph must be (q+1)-regular of diameter 6 on 2N vertices (Moore => hexagon)
    base = HERE / 'runs' / f'hexbase_q{q}.txt'
    with open(base, 'w') as fh:
        fh.write(f'{2 * N} {N * (q + 1)}\n')
        for k in range(N):
            for p in lines[k]:
                fh.write(f'{p} {N + k}\n')
    r = subprocess.run([str(HERE / 'tools' / 'check_big'), str(base), '6'], capture_output=True, text=True)
    log('base incidence graph:', r.stdout.strip())
    base.unlink()

if len(sys.argv) > 3 and sys.argv[3] == 'compare':
    ROOT = HERE.parents[2]
    sys.path.insert(0, str(ROOT / 'research' / 'gh6'))
    import gh_build
    ref = json.loads((ROOT / 'research' / 'gh6' / 'hex' / f'hexagon_q{q}.json').read_text())['lines']
    RP = gh_build.quadric_points(q)
    A = {frozenset(tuple(RP[p]) for p in L) for L in ref}
    Bset = {frozenset(tuple(int(c) for c in P[p]) for p in L) for L in lines}
    log('same line set as gh_build:', A == Bset)
    raise SystemExit


# ---------- incidence helpers
through = np.argsort(lines.ravel(), kind='stable').reshape(N, q + 1) // (q + 1)
lkey = lines[:, 0].astype(np.int64) * N + lines[:, 1]
lord = np.argsort(lkey)
lkey_sorted = lkey[lord]


def line_index(Lpts):
    """Lpts: (m, q+1) arrays of point indices (any order) -> line indices."""
    Ls = np.sort(Lpts, axis=1)
    k = Ls[:, 0].astype(np.int64) * N + Ls[:, 1]
    i = np.searchsorted(lkey_sorted, k)
    assert np.all(lkey_sorted[np.minimum(i, N - 1)] == k), 'not a line'
    return lord[i]


def perms(M):
    pp = index_of(fmatvec_rows(P, M))
    lp = line_index(pp[lines])
    return pp, lp


e = np.eye(7, dtype=np.int64)
v = int(line_index(np.array([[x for x in lines[through[index_of(e[1:2])[0]]].ravel()]]).reshape(-1, q + 1)[
    [any(index_of(e[6:7])[0] == y for y in L) for L in lines[through[index_of(e[1:2])[0]]]]])[0])
log('v =', v, P[lines[v][:2]].tolist())
# BFS distances from v in the incidence graph (points 0..N-1, lines N..2N-1)
dist = np.full(2 * N, -1)
dist[N + v] = 0
frontier = [N + v]
d = 0
while frontier:
    d += 1
    nxt = []
    for x in frontier:
        nb = (lines[x - N] if x >= N else (through[x] + N))
        for y in nb:
            if dist[y] < 0:
                dist[y] = d
                nxt.append(int(y))
    frontier = nxt
log('distances done; max', dist.max())
sq = {int(MUL[x, x]) for x in range(1, q)}
c = next(c for c in range(1, q) if int(NEG[c]) not in sq)
inH = ADD[P[:, 0], MUL[c, P[:, 4]]] == 0
S = np.nonzero(inH[lines].all(axis=1))[0]
assert len(S) == q ** 3 + 1 and v in set(S.tolist())
Sset = set(S.tolist())
Smask = np.zeros(N, bool)
Smask[S] = True
Sline_of = np.full(N, -1)
for s in S:
    Sline_of[lines[s]] = s
assert (Sline_of >= 0).sum() == (q ** 3 + 1) * (q + 1)
log('spread from X0 + %d X4 = 0' % c)
# root elements (generic coefficients) of the radical at v
ONE, TWO = 1, int(ADD[1, 1])
half = inv[TWO]
MONE = int(NEG[1])
RAD = [(((0, 2), (6, 4)), (1, MONE)), (((1, 0), (4, 5)), (1, MONE)), (((1, 2), (6, 5)), (1, MONE)),
       (((0, 5), (1, 4), (3, 2), (6, 3)), (1, MONE, 1, TWO)),
       (((1, 3), (3, 5), (4, 2), (6, 0)), (1, half, half, int(NEG[half])))]


def root(r, t):
    pat, cf = RAD[r]
    Nn = np.zeros((7, 7), dtype=np.int64)
    for (i, j), cc in zip(pat, cf):
        Nn[i, j] = MUL[t, cc]
    N2 = fmatmul(Nn, Nn)
    Id = np.eye(7, dtype=np.int64)
    return ADD[ADD[Id, Nn], MUL[half, N2]]


def word(ts):
    M = np.eye(7, dtype=np.int64)
    for r, t in enumerate(ts):  # x_{r1}(t1) first, then x_{r2}(t2), ...
        M = fmatmul(root(r, t), M)
    return M


def kelem(a, b, s):
    return word((a, b, s, int(MUL[c, b]), int(MUL[NEG[MUL[TWO, a]], inv[c]])))


basis = [int(F._exp[i]) for i in range(F.k)]  # 1, g, ..., g^(k-1): an additive basis of GF(q) over GF(p)
gens = {}
for name, f in (('A', lambda t: kelem(t, 0, 0)), ('B', lambda t: kelem(0, t, 0)), ('Z', lambda t: kelem(0, 0, t))):
    gens[name] = []
    for t in basis:
        pp, lp = perms(f(t))
        assert lp[v] == v and Smask[lp[S]].all(), name
        gens[name].append((pp, lp))
log('K_S generators fix v and S;', len(basis), 'additive generators')
g = GEN
T = np.diag([1, g, inv[g], 1, 1, inv[g], g]).astype(np.int64)
tp, tl = perms(T)
assert tl[v] == v and Smask[tl[S]].all()
log('torus element with g =', g)
free_pts = np.nonzero((Sline_of < 0) & (dist[:N] == 5))[0]
if LOAD:
    dd = json.loads((HERE / f'whiskers_big_q{q}.json').read_text())
    assert dd['v'] == v and dd['S'] == S.tolist()
    W = dd['whiskers']
    full_lines = sorted({int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in W})
    full_pts = lines[full_lines].ravel()
    cov = np.zeros(N, int)
    for k in W:
        cov[lines[k]] += 1
    okfree = bool(np.all(cov[free_pts] == 1))
    okX = bool(np.all(cov[full_pts] == 1))
    log('loaded', len(W), 'whiskers; free covered once', okfree, 'one per X', okX)
else:
    # blocks through v: off-S points at distance 3 from v
    offS = Sline_of < 0
    bv_pts = np.nonzero(offS & (dist[:N] == 3))[0]
    blocks_v = {}
    for p in bv_pts:
        B = frozenset(int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in through[p])
        blocks_v.setdefault(B, p)
    TV = sorted((sorted(B) for B in blocks_v), key=lambda b: b)
    assert len(TV) == q * q
    line_block = {}
    for i, B in enumerate(TV):
        for s in B:
            if s != v:
                line_block[s] = i
    # all blocks not through v, as sets of block-through-v indices they meet
    free_pts = np.nonzero(offS & (dist[:N] == 5))[0]
    seen_blocks = set()
    meet = []
    for p in free_pts:
        B = frozenset(int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in through[p])
        if B not in seen_blocks:
            seen_blocks.add(B)
            meet.append(frozenset(line_block[s] for s in B))
    log('blocks through v', len(TV), 'other blocks', len(meet))


    def bperm(lp):
        return [line_block[int(lp[TV[i][0] if TV[i][0] != v else TV[i][1]])] for i in range(len(TV))]


    bT = bperm(tl)
    bZs = [bperm(lp) for _, lp in gens['Z']]
    choice = None
    for (i, j) in [(1, 0)] + [(k, 1) for k in range(q)]:
        dgens = [perms(kelem(int(MUL[lam, i]), int(MUL[lam, j]), 0)) for lam in basis]
        bps = [bperm(lp) for _, lp in dgens] + bZs
        for b0 in range(len(TV)):
            orb = {b0}
            fr = [b0]
            while fr:
                nf = []
                for b in fr:
                    for bp_ in bps:
                        b2 = bp_[b]
                        if b2 not in orb:
                            orb.add(b2)
                            nf.append(b2)
                fr = nf
            if len(orb) == q and {bT[b] for b in orb} == orb and all(len(m & orb) <= 2 for m in meet):
                choice = ((i, j), sorted(orb), dgens)
                break
        if choice:
            break
    assert choice, 'no good invariant E'
    (i, j), Eb, dgens = choice
    log('direction', (i, j), 'E blocks', Eb)


    def compose_n(gp, n, base):
        out = base
        for _ in range(n):
            out = gp[out]
        return out


    # generator perms of K: Z and A^i B^j, plus the torus element
    def power_word(i, j):
        pp, lp = np.arange(N), np.arange(N)
        for _ in range(i):
            pp, lp = gens['A'][0][pp], gens['A'][1][lp]
        for _ in range(j):
            pp, lp = gens['B'][0][pp], gens['B'][1][lp]
        return pp, lp


    GENS = gens['Z'] + dgens + [(tp, tl)]
    E = set()
    for b in Eb:
        E |= set(TV[b]) - {v}
    full_lines = [s for s in S if s != v and s not in E]
    full_pts = lines[full_lines].ravel()
    isfull = np.zeros(N, bool)
    isfull[full_pts] = True
    # candidates: lines opposite v, not in S, through a point of a full S-line
    cand_mask = (dist[N:] == 6) & ~Smask & isfull[lines].any(axis=1)
    cand = np.nonzero(cand_mask)[0]
    log('free points', len(free_pts), 'X-points', len(full_pts), 'candidates', len(cand))


    def orbits(items, which):
        """union-find orbits of the group generated by GENS on items (points: which=0, lines: which=1)"""
        parent = {int(x): int(x) for x in items}

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        for gg in GENS:
            img = gg[which][items]
            for a, b in zip(items, img):
                ra, rb = find(int(a)), find(int(b))
                if ra != rb:
                    parent[ra] = rb
        return {x: find(x) for x in parent}


    oc = orbits(cand, 1)
    op = orbits(free_pts, 0)
    ox = orbits(full_pts, 0)
    creps = sorted(set(oc.values()))
    preps = sorted(set(op.values()))
    xreps = sorted(set(ox.values()))
    log('orbits: candidates', len(creps), 'free points', len(preps), 'X-points', len(xreps))
    ci = {r: n for n, r in enumerate(creps)}
    pi_ = {r: n for n, r in enumerate(preps)}
    xi_ = {r: len(preps) + n for n, r in enumerate(xreps)}
    A = lil_matrix((len(preps) + len(xreps), len(creps)))
    # count, for each orbit pair, incidences of all members, then divide by the orbit size of the row
    rowsize = Counter()
    for p in free_pts:
        rowsize[pi_[op[int(p)]]] += 1
    for X in full_pts:
        rowsize[xi_[ox[int(X)]]] += 1
    acc = Counter()
    for k in cand:
        col = ci[oc[int(k)]]
        for y in lines[k]:
            y = int(y)
            if y in op:
                acc[(pi_[op[y]], col)] += 1
            elif y in ox:
                acc[(xi_[ox[y]], col)] += 1
    for (r, cc), val in acc.items():
        A[r, cc] = val / rowsize[r]
    res = milp(np.zeros(len(creps)), constraints=[LinearConstraint(A.tocsr(), 1, 1)], integrality=np.ones(len(creps)),
               bounds=Bounds(0, 1), options={'time_limit': secs})
    log('ILP:', res.message)
    if res.status != 0:
        raise SystemExit
    chosen = {creps[n] for n in range(len(creps)) if res.x[n] > 0.5}
    W = sorted(int(k) for k in cand if oc[int(k)] in chosen)
    cov = np.zeros(N, int)
    for k in W:
        cov[lines[k]] += 1
    okfree = np.all(cov[free_pts] == 1)
    okX = np.all(cov[full_pts] == 1)
    log('whiskers', len(W), 'expected', q * q * (q * q - 1), 'free covered once', bool(okfree), 'one per X', bool(okX))
    (HERE / f'whiskers_big_q{q}.json').write_text(json.dumps({'q': q, 'c': c, 'v': v, 'S': S.tolist(), 'whiskers': W,
                                                              'E_blocks': [TV[b] for b in Eb]}))
if build and okfree and okX:
    lev = np.full(2 * N, -1)
    for s in S:
        if s != v:
            lev[N + s] = 1
            lev[lines[s]] = 0
    lev[N + v] = 2
    for p in lines[v]:
        lev[p] = 1
        for k in through[p]:
            if k != v:
                lev[N + k] = 0
    for k in W:
        assert lev[N + k] == -1
        lev[N + k] = 0
    # Delorme versions: vertex x of level L has 2^(L+1) versions (strings), level -1 one version
    m_ = ARITY
    nver = np.where(lev < 0, 1, m_ ** (lev + 1))
    first = np.concatenate([[0], np.cumsum(nver)[:-1]])
    n = int(nver.sum())
    out = HERE / 'runs' / f'hex_q{q}_a{ARITY}_big.txt'
    m = 0
    with open(out, 'w') as fh:
        fh.write(' ' * 40 + '\n')
        for k in range(N):
            for p in lines[k]:
                a, b = (int(p), N + k)
                la, lb = int(lev[a]), int(lev[b])
                if la > lb:
                    a, b, la, lb = b, a, lb, la
                # versions: strings of length la+1 (or empty) for a; extensions of length lb+1 for b
                na = 1 if la < 0 else m_ ** (la + 1)
                ext = 1 if lb < 0 else m_ ** (lb + 1 - (la + 1 if la >= 0 else 0))
                for ia in range(na):
                    for e2 in range(ext):
                        ib = ia * ext + e2 if la >= 0 else e2
                        fh.write(f'{first[a] + ia} {first[b] + ib}\n')
                        m += 1
    with open(out, 'r+') as fh:
        fh.write(f'{n} {m}')
    log('graph', n, 'vertices', m, 'edges ->', out)
    r = subprocess.run([str(HERE / 'diam'), str(out), '6'], capture_output=True, text=True)
    log('diam:', r.stdout.strip())
    r = subprocess.run([str(HERE / 'tools' / 'check_big'), str(out), '6'], capture_output=True, text=True)
    log('check_big:', r.stdout.strip())
