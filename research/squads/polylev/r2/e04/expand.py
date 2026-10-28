"""Expand an independent set of orbits (mis2 output: quotient indices, one per line) to points, then optionally add
free points greedily (a point is addable iff none of its 14 lines already holds a chosen point).
usage: expand.py MIS_TXT OUT_PREFIX [GREEDY 0|1] [SEED]
Writes OUT_PREFIX.txt (one point id per line) and prints the counts. The output is checked independently by certify.py."""
import struct, sys, numpy as np

HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q13.bin'
WORK = '/home/user/degree-diameter/research/squads/polylev/r2/e04/work'
mis_file, out_prefix = sys.argv[1], sys.argv[2]
greedy = int(sys.argv[3]) if len(sys.argv) > 3 else 1
seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1

with open(HEX, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1).astype(np.int64)
qorb = np.fromfile(WORK + '/Q_orb.bin', dtype=np.int32).astype(np.int64)
orb = np.fromfile(WORK + '/orb.bin', dtype=np.int32).astype(np.int64)
chosen_q = np.loadtxt(mis_file, dtype=np.int64, ndmin=1)
chosen_orbs = np.unique(qorb[chosen_q])
inS = np.isin(orb, chosen_orbs)
print('orbits chosen', len(chosen_orbs), 'points from orbits', int(inS.sum()), flush=True)

if greedy:
    flat = lines.ravel()
    order = np.argsort(flat, kind='stable')
    PL = (order // (q + 1)).reshape(N, q + 1)
    cnt = np.zeros(L, dtype=np.int64)       # cnt[l] = number of chosen points on line l
    np.add.at(cnt, PL[inS].ravel(), 1)
    cand = np.nonzero(~inS)[0]
    rng = np.random.default_rng(seed)
    rng.shuffle(cand)
    added = 0
    for p in cand:
        ls = PL[p]
        if (cnt[ls] == 0).all():
            inS[p] = True
            cnt[ls] += 1
            added += 1
    print('greedy point completion added', added, flush=True)

pts = np.nonzero(inS)[0]
np.savetxt(out_prefix + '.txt', pts, fmt='%d')
print('final set size', len(pts), flush=True)
