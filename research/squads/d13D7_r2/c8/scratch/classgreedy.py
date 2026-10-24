# card c8: class-greedy for mode 0 (middles = Hermitian spread lines). Each step opens the spread class with the most points
# that still have a free line (distance > 4 from every chosen line), takes one free line per such point (least damage).
import sys, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
N, L = len(coord), len(lines)
LP = np.asarray(lines, dtype=np.int64)
lines_of = [[] for _ in range(N)]
for l in range(L):
    for p in LP[l]:
        lines_of[p].append(l)
PL = np.array(lines_of, dtype=np.int64)
isSp = ((coord[LP][:, :, 0].astype(int) + coord[LP][:, :, 4].astype(int)) % q == 0).all(axis=1)
SP = np.nonzero(isSp)[0]
def ball4(l):
    P = LP[l]
    M = PL[P].ravel()
    M = M[M != l]
    R = LP[M]                     # (132, 12) points on the distance-2 lines
    pP = np.repeat(P, Q1 - 1)     # the point p through which M was reached
    keep = R != pP[:, None]
    Rk = R[keep]
    Mrep = np.repeat(M, Q1 - 1)
    Nn = PL[Rk]                   # (132*11, 12)
    Nn = Nn[Nn != Mrep[:, None]]
    return np.concatenate([M, Nn])
Q1 = q + 1
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
random.seed(seed); rng = np.random.default_rng(seed)
cnt = np.zeros(L, dtype=np.int32)
inS = np.zeros(L, dtype=bool)
chosen_cls = []
S = []
used = set()
MAXSTAR = 11
def free_mask():
    return (cnt == 0) & (~inS) & (~isSp)
steps = 0
while len(chosen_cls) < 121:
    fr = free_mask()
    fl = LP[fr]
    freeAt = np.bincount(fl.ravel(), minlength=N)
    # gain per spread class: points on m with freeAt>0
    pts_ok = (freeAt[LP[SP]] > 0)     # (1332, 12)
    gain = pts_ok.sum(axis=1)
    gain[[i for i, m in enumerate(SP) if m in used]] = -1
    best = gain.max()
    if best <= 0: break
    cands = np.nonzero(gain == best)[0]
    ci = int(rng.choice(cands))
    m = int(SP[ci])
    # choose one free line per point of m (least damage among candidates)
    add = []
    for k, x in enumerate(LP[m]):
        if not pts_ok[ci, k]: continue
        opts = [l for l in PL[x] if l != m and fr[l]]
        if MAXSTAR and len(add) >= MAXSTAR: break
        if len(opts) == 1:
            add.append(int(opts[0])); continue
        # damage = number of currently free lines within distance 4 of the option
        dmg = [int(fr[ball4(l)].sum()) for l in opts]
        add.append(int(opts[int(np.argmin(dmg))]))
    add = add[:MAXSTAR]
    for l in add:
        inS[l] = True
        cnt[ball4(l)] += 1
    S += [(m, l) for l in add]
    used.add(m); chosen_cls.append(m)
    steps += 1
    print('step', steps, 'class', m, 'gain', int(best), 'added', len(add), 'total', len(S), flush=True)
out = sys.argv[2] if len(sys.argv) > 2 else '/home/user/degree-diameter/research/squads/d13D7_r2/c8/greedy_stars.txt'
groups = {}
for m, l in S: groups.setdefault(m, []).append(l)
with open(out, 'w') as f:
    for m in groups: f.write(' '.join(map(str, [m] + groups[m])) + '\n')
print('TOTAL', len(S), 'stars', len(groups), file=sys.stderr)
