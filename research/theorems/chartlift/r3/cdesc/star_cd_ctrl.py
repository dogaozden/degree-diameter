"""Coordinate descent over star collineations (Lemma 5) for k-letter charts over F_q^4, q prime.
State: points w_c (A-space) and b_c (B-space), and for each letter a collineation sigma_c: star(w_c) -> star(b_c).
U(c;t) = sigma_c^-1(b_c b_t), V(c;t) = sigma_c(w_c w_t).  Cost = singular patterns + BIG*(incomplete pencils +
uncovered diagonal points).  A move re-optimises ONE letter's sigma exhaustively over all of PGL(3,q) (5,616 maps for
q = 3) with the other letters fixed; we cycle through letters, with random kicks when stuck.  The result is lifted to
matrices A_c (A_c w_c = b_c) and written in chart_anneal format (gauge A_0 = I); check it with chartflags.py.
usage: python3 star_cd.py q k INIT_CHART SECONDS SEED out.txt
Controller-aware variant (star_cd_ctrl.py): env CTRL=volt_file and GROUP=group_table_file (a Haar or voltage
controller from ctrl_search); the objective becomes BIG*(holes + pencil fails) + 10*(uncovered controller targets)
+ singular, i.e. the chart is optimised for that controller (Theorem 11 conditions)."""
import itertools, sys, random, time
q, k, initp, secs, seed, outp = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], float(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
rng = random.Random(seed); BIG = 1000
def norm(v):
    for x in v:
        if x % q: inv = pow(x, q - 2, q); return tuple((y * inv) % q for y in v)
PTS = sorted({norm(v) for v in itertools.product(range(q), repeat=4) if any(v)}); IDX = {p: i for i, p in enumerate(PTS)}
NP = len(PTS); FULL = (1 << NP) - 1
def span(vs):
    out = set()
    for cs in itertools.product(range(q), repeat=len(vs)):
        v = [sum(c * x[i] for c, x in zip(cs, vs)) % q for i in range(4)]
        if any(v): out.add(norm(v))
    return out
def mask(ps): return sum(1 << IDX[p] for p in ps)
def pmask(v): return 1 << IDX[norm(v)]
LINE = {}
def line(a, b):
    key = (norm(a), norm(b))
    if key not in LINE: LINE[key] = mask(span([a, b]))
    return LINE[key]
PLANES = sorted({mask(span([a, b, c])) for a, b, c in itertools.combinations(PTS, 3) if len(span([a, b, c])) == (q ** 3 - 1) // (q - 1)})
def matvec(M, v): return [sum(M[i][j] * v[j] for j in range(len(v))) % q for i in range(len(M))]
def inv(M):
    n = len(M); T = [list(M[r]) + [int(r == c) for c in range(n)] for r in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if T[r][c] % q); T[c], T[p] = T[p], T[c]
        iv = pow(T[c][c], q - 2, q); T[c] = [(x * iv) % q for x in T[c]]
        for r in range(n):
            if r != c and T[r][c] % q: f = T[r][c]; T[r] = [(x - f * y) % q for x, y in zip(T[r], T[c])]
    return [row[n:] for row in T]
def rank(vs):
    rows = [list(v) for v in vs]; r = 0
    for c in range(len(rows[0])):
        p = next((i for i in range(r, len(rows)) if rows[i][c] % q), None)
        if p is None: continue
        rows[r], rows[p] = rows[p], rows[r]; iv = pow(rows[r][c], q - 2, q); rows[r] = [(x * iv) % q for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % q: f = rows[i][c]; rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
        r += 1
    return r
# read the initial chart
vals = [list(map(int, l.split())) for l in open(initp) if l.strip()]
A = [[v[4 * r:4 * r + 4] for r in range(4)] for v in vals[:k]]; Bv = [v for v in vals[k:2 * k]]
Wv = [matvec(inv(A[c]), Bv[c]) for c in range(k)]
E = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]
def compl(p):
    out = []
    for c in E:
        if rank([p] + out + [c]) == 2 + len(out): out.append(c)
        if len(out) == 3: return out
BW = [compl(Wv[c]) for c in range(k)]; BB = [compl(Bv[c]) for c in range(k)]
PG2 = sorted({norm(v + (0,))[:3] for v in itertools.product(range(q), repeat=3) if any(v)})
def vec(basis, d): return [sum(c * x[i] for c, x in zip(d, basis)) % q for i in range(4)]
def coords(p, basis, v):
    for d in PG2:
        for a in range(q):
            w = [(a * p[i] + vec(basis, d)[i]) % q for i in range(4)]
            if any(w) and norm(w) == norm(v): return d
MATS = []
for ent in itertools.product(range(q), repeat=9):
    M = [list(ent[0:3]), list(ent[3:6]), list(ent[6:9])]
    if next((x for x in ent if x), 0) == 1 and rank(M) == 3: MATS.append(M)
def app(M, d): return norm(tuple(matvec(M, list(d))) + (0,))[:3]
LA = [{d: line(Wv[c], vec(BW[c], d)) for d in PG2} for c in range(k)]   # line through w_c with star direction d
LB = [{d: line(Bv[c], vec(BB[c], d)) for d in PG2} for c in range(k)]
others = [[t for t in range(k) if t != c] for c in range(k)]
dE = [[coords(Wv[c], BW[c], Wv[t]) for t in others[c]] for c in range(k)]    # direction of w_c w_t in star(w_c)
dEp = [[coords(Bv[c], BB[c], Bv[t]) for t in others[c]] for c in range(k)]   # direction of b_c b_t in star(b_c)
# per letter, per collineation: labelled U-lines and V-lines
CAND = []
for c in range(k):
    lst = []
    for M in MATS:
        Mi = inv(M)
        U = tuple(LA[c][app(Mi, d)] for d in dEp[c]); V = tuple(LB[c][app(M, d)] for d in dE[c])
        lst.append((U, V, M))
    CAND.append(lst)
# current sigma: the one induced by the initial A_c
def induced(c):
    Ac = A[c]
    imgs = []
    for d in [(1, 0, 0), (0, 1, 0), (0, 0, 1)]:
        v = matvec(Ac, vec(BW[c], d)); imgs.append(coords(Bv[c], BB[c], v))
    # sigma maps basis directions to imgs only up to scalars; pick the candidate with the same U and V lines as A_c gives
    U = tuple(line(matvec(inv(Ac), Bv[c]), matvec(inv(Ac), Bv[t])) for t in others[c])
    V = tuple(line(matvec(Ac, Wv[c]), matvec(Ac, Wv[t])) for t in others[c])
    for i, (u, v, M) in enumerate(CAND[c]):
        if u == U and v == V: return i
    raise ValueError('induced collineation not found')
cur = [induced(c) for c in range(k)]
wpt = [pmask(w) for w in Wv]; bpt = [pmask(b) for b in Bv]
EA = 0; EB = 0
for s in range(k): EA |= wpt[s]; EB |= bpt[s]
for s, t in itertools.combinations(range(k), 2): EA |= line(Wv[s], Wv[t]); EB |= line(Bv[s], Bv[t])
LBB = {(i, j): line(Bv[i], Bv[j]) for i in range(k) for j in range(k) if i != j}
LWW = {(i, j): line(Wv[i], Wv[j]) for i in range(k) for j in range(k) if i != j}
def pencil_ok(L, lines, pts):
    for P in PLANES:
        if P & L != L: continue
        if any(l != L and (P & l) == l for l in lines): continue
        if any((P & p) and not (p & L) for p in pts): continue
        return False
    return True
def cost(sel):
    U = [CAND[c][sel[c]][0] for c in range(k)]; V = [CAND[c][sel[c]][1] for c in range(k)]
    sing = 0
    for s, s2 in itertools.combinations(range(k), 2):
        for x in U[s]:
            for y in U[s2]:
                if x & y: sing += 2
        for x in V[s]:
            for y in V[s2]:
                if x & y: sing += 2
    da = EA; db = EB
    for c in range(k):
        for x in U[c]: da |= x
        for x in V[c]: db |= x
    holes = bin(FULL & ~da).count('1') + bin(FULL & ~db).count('1')
    pf = 0
    for i, j in itertools.combinations(range(k), 2):
        rest = [t for t in range(k) if t not in (i, j)]
        if not pencil_ok(LBB[(i, j)], list(V[i]) + list(V[j]), [bpt[t] for t in rest]): pf += 1
        if not pencil_ok(LWW[(i, j)], list(U[i]) + list(U[j]), [wpt[t] for t in rest]): pf += 1
    if CTRLW is not None:
        cu = ctrl_uncovered(U, V)
        return sing + BIG * (holes + pf) + 10 * cu, sing, holes, pf, cu
    return sing + BIG * (holes + pf), sing, holes, pf

import os
CTRLW = None
if os.environ.get('CTRL'):
    rowsv = [list(map(int, l.split())) for l in open(os.environ['CTRL']) if l.strip()]
    r_, k_, g_ = rowsv[0]; assert k_ == k
    base = [tuple(x) for x in rowsv[1:]]
    gl = open(os.environ['GROUP']).read().split('\n'); gT = list(map(int, gl[1].split())); gN = int(gl[0])
    gid = next(i for i in range(gN) if all(gT[i * gN + j] == j for j in range(gN)))
    ginv = [next(j for j in range(gN) if gT[i * gN + j] == gid) for i in range(gN)]
    gm = lambda a, b: gT[a * gN + b]
    # side A walks from base vertex i: edges (i, j, c, v): A->B multiply by v, B->A by v^-1 (as in ctrl_search walk_elt)
    E_ = base
    CTRLW = [dict(), dict()]   # side -> {(start, end, element): [patterns]} for 4-walks; 2-walk targets in CTRL2
    CTRL2 = [set(), set()]
    for side in range(2):
        X = (lambda e: e[0]) if side == 0 else (lambda e: e[1]); Y = (lambda e: e[1]) if side == 0 else (lambda e: e[0])
        for i in range(r_):
            for e1 in E_:
                if X(e1) != i: continue
                for e2 in E_:
                    if e2 is e1 or Y(e2) != Y(e1): continue
                    if side == 0: x2 = gm(ginv[e2[3]], e1[3])
                    else: x2 = gm(e2[3], ginv[e1[3]])
                    if not (X(e2) == i and x2 == gid): CTRL2[side].add((i, X(e2), x2))
                    for e3 in E_:
                        if e3 is e2 or X(e3) != X(e2): continue
                        for e4 in E_:
                            if e4 is e3 or Y(e4) != Y(e3): continue
                            if side == 0: x = gm(ginv[e4[3]], gm(e3[3], gm(ginv[e2[3]], e1[3])))
                            else: x = gm(e4[3], gm(ginv[e3[3]], gm(e2[3], ginv[e1[3]])))
                            CTRLW[side].setdefault((i, X(e4), x), []).append((e1[2], e2[2], e3[2], e4[2]))
    print('controller loaded: r=%d |G|=%d, 4-walk targets %d/%d' % (r_, gN, len(CTRLW[0]), len(CTRLW[1])), flush=True)
def ctrl_uncovered(U, V):
    unc = 0
    for side in range(2):
        L = U if side == 0 else V
        # pattern (i1,i2,i3,i4) singular iff line (i2;i1) meets line (i3;i4); L[c] lists lines for t in others[c]
        pos = lambda c, t: t if t < c else t - 1
        cov = set(CTRL2[side])
        for key, pats in CTRLW[side].items():
            if key in cov: continue
            for (a, b, c, d) in pats:
                if not (L[b][pos(b, a)] & L[c][pos(c, d)]): cov.add(key); break
        total = r_ * gN * r_ - r_          # targets (end base vertex, element) excluding (i, identity) for each start i
        unc += sum(1 for i in range(r_) for j in range(r_) for x in range(gN) if not (i == j and x == gid) and (i, j, x) not in cov)
    return unc
def write_chart(sel, path):
    # lift best to matrices: A_c w_c = b_c, A_c bw_i = sum_j M[j][i] bb_j
    out = []
    for c in range(k):
        M = CAND[c][sel[c]][2]
        src = [list(Wv[c])] + [list(v) for v in BW[c]]; dst = [list(Bv[c])] + [vec(BB[c], [M[j][i] for j in range(3)]) for i in range(3)]
        S = [[src[cc][r] for cc in range(4)] for r in range(4)]; D = [[dst[cc][r] for cc in range(4)] for r in range(4)]
        Si = inv(S); out.append([[sum(D[i][t] * Si[t][j] for t in range(4)) % q for j in range(4)] for i in range(4)])
    G = inv(out[0]); out = [[[sum(Ac[i][t] * G[t][j] for t in range(4)) % q for j in range(4)] for i in range(4)] for Ac in out]
    with open(path, 'w') as f:
        for Ac in out: f.write(' '.join(str(x) for row in Ac for x in row) + ' \n')
        for c in range(k): f.write(' '.join(map(str, Bv[c])) + ' \n')
    print('wrote', path)
    
best = list(cur); bc = cost(cur); print('start', bc, flush=True)
t0 = time.time(); stale = 0
while time.time() - t0 < secs:
    improved = False
    for c in rng.sample(range(k), k):
        scores = []
        for i in range(len(CAND[c])):
            sel = list(cur); sel[c] = i
            scores.append((cost(sel)[0], rng.random(), i))
        scores.sort()
        if scores[0][0] < cost(cur)[0]: cur[c] = scores[0][2]; improved = True
    cc = cost(cur)
    if cc[0] < bc[0]:
        best = list(cur); bc = cc; print('t=%.0fs best' % (time.time() - t0), bc, flush=True)
        if CTRLW is not None and cc[4] == 0: write_chart(best, outp + '.cu0')
    if not improved:
        stale += 1; c = rng.randrange(k); cur = list(best); cur[c] = rng.randrange(len(CAND[c]))   # kick
print('FINAL', bc, flush=True)
write_chart(best, outp)
