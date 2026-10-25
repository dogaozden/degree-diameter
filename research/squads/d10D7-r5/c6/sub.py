# Orbit-level k-fixed tabu for a subgroup H = <g^(91/h)> of the order-91 group (h = 13 or 7 = orbit size).
# usage: sub.py H K SECONDS SEED OUTFILE
import pickle, sys, time, struct
import numpy as np
H = int(sys.argv[1]); K = int(sys.argv[2]); SECS = float(sys.argv[3]); SEED = int(sys.argv[4]); OUT = sys.argv[5]
FN = '/home/user/degree-diameter/research/d10D7/hex/hex_q9.bin'
data = open(FN, 'rb').read()
q, N, _ = struct.unpack_from('<iii', data, 0)
LP = np.frombuffer(data, dtype='<i4', count=N*10, offset=12).reshape(N, 10).astype(np.int64).copy()
perm = pickle.load(open('/home/user/degree-diameter/research/squads/d10D7-r5/c6/grp.pkl', 'rb'))['perm'].astype(np.int64)
flat = LP.ravel(); lines_of = np.repeat(np.arange(N), 10)
PL = lines_of[np.argsort(flat, kind='stable')].reshape(N, 10)
allp = LP[PL]; mask = allp != np.arange(N)[:, None, None]
NB = allp[mask].reshape(N, 90)
# subgroup generator: perm^(91/H)
e = 91 // H
hp = np.arange(N)
base = perm.copy(); pw = np.arange(N)
k = e
while k:
    if k & 1: pw = base[pw]
    base = base[base]; k >>= 1
hperm = pw
orbit_of = -np.ones(N, np.int64); orbits = []
for p in range(N):
    if orbit_of[p] >= 0: continue
    cyc = []; x = p
    while True:
        cyc.append(x); orbit_of[x] = len(orbits); x = hperm[x]
        if x == p: break
    orbits.append(cyc)
M = len(orbits)
sizes = np.array([len(c) for c in orbits]); assert np.all(sizes == H), np.unique(sizes)
same = orbit_of[NB] == orbit_of[:, None]
bad = np.zeros(M, bool); bad[orbit_of[np.nonzero(same.any(axis=1))[0]]] = True
good = np.nonzero(~bad)[0]
gid = -np.ones(M, np.int64); gid[good] = np.arange(len(good))
n = len(good)
Am = np.zeros((M, M), bool)
Am[orbit_of[:, None].repeat(90, 1), orbit_of[NB]] = True
np.fill_diagonal(Am, False)
A = Am[np.ix_(good, good)].astype(np.int32)
print('H', H, 'orbits', M, 'self-compatible', n, 'conflict density %.4f' % (A.sum() / max(1, n*(n-1))), flush=True)
rng = np.random.default_rng(SEED)
t0 = time.time(); best_out = None; it = 0
while time.time() - t0 < SECS and best_out is None:
    inS = np.zeros(n, bool)
    inS[rng.choice(n, K, replace=False)] = True
    conf = A @ inS.astype(np.int32)
    tabu_in = np.zeros(n, np.int64); tabu_out = np.zeros(n, np.int64)
    tt = 7 + int(rng.integers(0, 5))
    for step in range(10**9):
        it += 1
        if step % 512 == 0 and time.time() - t0 > SECS: break
        cf = conf[inS]
        if cf.max() == 0:
            best_out = np.nonzero(inS)[0]; break
        cand = np.nonzero(inS & (conf > 0) & (tabu_out <= step))[0]
        if len(cand) == 0: cand = np.nonzero(inS & (conf > 0))[0]
        cu = conf[cand]; m = cu.max(); cu = cand[cu == m]
        u = int(cu[rng.integers(len(cu))])
        inS[u] = False; conf -= A[u]
        score = conf + rng.random(n) * 0.5
        score[inS] = 1e9
        score[tabu_in > step] = 1e9
        v = int(np.argmin(score))
        inS[v] = True; conf += A[v]
        tabu_in[u] = step + tt + int(rng.integers(0, 3))
        tabu_out[v] = step + 3
        if step % 2000 == 1999: tt = 7 + int(rng.integers(0, 5))
print('H', H, 'K', K, 'iters', it, 'time %.1f' % (time.time() - t0), 'found' if best_out is not None else 'NOT found', flush=True)
if best_out is not None:
    pts = []
    for o in best_out: pts += orbits[good[o]]
    pts = sorted(pts)
    open(OUT, 'w').write('\n'.join(map(str, pts)) + '\n')
    print('wrote', len(pts), 'points to', OUT, flush=True)
