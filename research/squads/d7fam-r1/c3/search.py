"""Card c3: exact-scored best-response search over extras (x_j, L_j) with R fixed (72 base points).
Score = sum_t min(c_t, p_t) + k, c_t = #R points with type t (type = bits [r perp x_j]),
p_t = #usable spread lines with type t (type = bits [s at distance 4 from L_j]; each L_j kills its one concurrent spread line).
Pairwise: X pairwise opposite, L pairwise opposite, L not in S, X non-collinear with R."""
import numpy as np, sys, time, random
HERE = '/home/user/degree-diameter/research/squads/d7fam-r1/c3'
sys.path.insert(0, HERE)
from hexmod import Hex
SQ = '/tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq'
SECS = float(sys.argv[1]) if len(sys.argv) > 1 else 300
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
rng = random.Random(seed)
t0 = time.time()
H = Hex(SQ + '/hex_q5.bin'); N = H.N
R = np.load(SQ + '/R_q5.npy').astype(np.int64)
S = np.load(SQ + '/S_q5.npy').astype(np.int64); nS = len(S)
Sset = set(S.tolist())
st = np.load(SQ + '/state_q5_F9.npz'); X0 = [int(v) for v in st['X']]; L0 = [int(v) for v in st['L']]
Rset = set(R.tolist())
coll_R = set()
for r in R: coll_R |= H.collinear_points(int(r))
cx = np.array([p for p in range(N) if p not in coll_R and p not in Rset], dtype=np.int64); nx = len(cx)
BX = (H.Bmat(cx, R) == 0).astype(np.int64)            # (nx, 72): x perp r (distance 4)
OPX = (H.Bmat(cx, cx) != 0)                           # pairwise opposite
cl = np.array([l for l in range(N) if l not in Sset], dtype=np.int64); nl = len(cl)
cS = np.zeros((nl, nS), np.int64); exc = -np.ones(nl, np.int64); OPL = np.zeros((nl, nl), bool)
Sidx = {int(s): i for i, s in enumerate(S)}
for i, l in enumerate(cl):
    d2, d4 = H.line_ball(int(l))
    m2 = np.zeros(N, bool); m2[list(d2)] = True
    m4 = np.zeros(N, bool); m4[list(d4)] = True
    OPL[i] = ~(m2 | m4)[cl]; OPL[i, i] = False
    cS[i] = m4[S]
    c = [Sidx[s] for s in S[m2[S]]]
    assert len(c) == 1, len(c)
    exc[i] = c[0]
print('precompute done', round(time.time() - t0, 1), 's; nx', nx, 'nl', nl, flush=True)
cpos = {int(v): i for i, v in enumerate(cx)}; lpos = {int(v): i for i, v in enumerate(cl)}

def score(xi, li):
    k = len(xi)
    rt = np.zeros(len(R), np.int64); st_ = np.zeros(nS, np.int64)
    for j in range(k):
        rt += BX[xi[j]] << j
        st_ += cS[li[j]] << j
    pool = np.ones(nS, bool); pool[exc[list(li)]] = False
    u, c = np.unique(rt, return_counts=True)
    pu, pc = np.unique(st_[pool], return_counts=True)
    idx = np.searchsorted(pu, u); idx = np.minimum(idx, len(pu) - 1)
    p = np.where(pu[idx] == u, pc[idx], 0)
    return int(np.minimum(c, p).sum()) + k

def valid(xi, li):
    k = len(xi)
    return all(OPX[xi[a], xi[b]] for a in range(k) for b in range(a + 1, k)) and \
           all(OPL[li[a], li[b]] for a in range(k) for b in range(a + 1, k))

xi = [cpos[x] for x in X0]; li = [lpos[l] for l in L0]
assert valid(xi, li)
cur = score(xi, li); print('baseline score (F9 state, expect 81):', cur, flush=True)
best = (cur, list(xi), list(li))

def best_replace_x(xi, li, j):
    k = len(xi); others = [xi[i] for i in range(k) if i != j]
    ok = OPX[:, others].all(axis=1) if others else np.ones(nx, bool)
    ok[others] = False
    cand = np.nonzero(ok)[0]; bs = -1; bl = []
    for x in cand:
        xi2 = list(xi); xi2[j] = int(x); s = score(xi2, li)
        if s > bs: bs, bl = s, [int(x)]
        elif s == bs: bl.append(int(x))
    return bs, rng.choice(bl)

def best_replace_l(xi, li, j):
    k = len(li); others = [li[i] for i in range(k) if i != j]
    ok = OPL[:, others].all(axis=1) if others else np.ones(nl, bool)
    ok[others] = False
    cand = np.nonzero(ok)[0]; bs = -1; bl = []
    for l in cand:
        li2 = list(li); li2[j] = int(l)
        if len(set(exc[li2].tolist())) < k: continue
        s = score(xi, li2)
        if s > bs: bs, bl = s, [int(l)]
        elif s == bs: bl.append(int(l))
    return bs, rng.choice(bl)

def try_add(xi, li, nsamp=60):
    k = len(xi); bs = -1; bc = None
    xs = np.arange(nx)
    ok_x = OPX[:, xi].all(axis=1) if k else np.ones(nx, bool)
    ok_x[xi] = False
    cand_x = np.nonzero(ok_x)[0]
    ok_l = OPL[:, li].all(axis=1) if k else np.ones(nl, bool)
    cand_l = np.nonzero(ok_l)[0]
    if len(cand_l) == 0: return None
    for x in cand_x:
        for l in rng.sample(list(cand_l), min(nsamp, len(cand_l))):
            if exc[l] in set(exc[li].tolist()): continue
            s = score(xi + [int(x)], li + [int(l)])
            if s > bs: bs, bc = s, (int(x), int(l))
    return bs, bc

tlast = time.time(); it = 0
while time.time() - t0 < SECS:
    it += 1
    improved = False
    for j in range(len(xi)):
        s, x = best_replace_x(xi, li, j)
        if s >= cur: xi[j] = x
        cur = score(xi, li)
        s, l = best_replace_l(xi, li, j)
        if s >= cur: li[j] = l
        cur = score(xi, li)
        if cur > best[0]:
            best = (cur, list(xi), list(li)); improved = True
            print(f'it {it} pos {j}: new best {cur} k={len(xi)} t={time.time()-t0:.0f}s', flush=True)
    if not improved:
        # add move if possible, else kick (replace a random position by a random valid candidate)
        r = try_add(xi, li)
        if r is not None and r[0] >= cur - 1:
            xi.append(r[1][0]); li.append(r[1][1]); cur = score(xi, li)
            print(f'it {it}: added -> score {cur} k={len(xi)} t={time.time()-t0:.0f}s', flush=True)
        else:
            j = rng.randrange(len(xi)); xi.pop(j); li.pop(j); cur = score(xi, li)
            print(f'it {it}: dropped pos {j} -> score {cur} k={len(xi)}', flush=True)
        if cur > best[0]:
            best = (cur, list(xi), list(li))
    if not valid(xi, li):
        print('INVALID state, reverting to best', flush=True); xi, li = list(best[1]), list(best[2]); cur = best[0]
    if time.time() - tlast > 60:
        tlast = time.time(); print(f'  it {it} cur {cur} best {best[0]} k={len(xi)} t={time.time()-t0:.0f}s', flush=True)

bs, bxi, bli = best
print('BEST', bs, 'k', len(bxi), flush=True)
np.savez(HERE + f'/state_c3_s{seed}.npz', R=R, X=cx[np.array(bxi)], L=cl[np.array(bli)])
print('saved', HERE + f'/state_c3_s{seed}.npz')
