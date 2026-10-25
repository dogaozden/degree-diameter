#!/usr/bin/env python3
"""c3: build extra-point sets X with NO base point in three or more neighbourhoods N(x) (coverage <= 2),
X pairwise opposite, X non-collinear with R756.  Randomised greedy (least overlap first) with restarts.
usage: build_x.py SEED RESTARTS OUT.npy"""
import numpy as np, sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
seed = int(sys.argv[1]); restarts = int(sys.argv[2]); out = sys.argv[3]
rng = np.random.default_rng(seed); t0 = time.time()
H = Hex(SP + 'hex_q11.bin'); N = H.N
R = np.load(SP + 'R756idx.npy')
colR = np.zeros(N, bool); colR[H.lp[H.pl[R]].reshape(-1)] = True; colR[R] = True
cand = np.nonzero(~colR)[0]; nc = len(cand)
NRb = np.zeros((nc, len(R)), bool)
for a in range(0, nc, 8192):
    NRb[a:a + 8192] = (H.Bmat(cand[a:a + 8192], R) == 0)
NRf = NRb.astype(np.float32)
cnt = NRb.sum(1)
print(f'candidates {nc}; |N(x)| min {cnt.min()} max {cnt.max()} mean {cnt.mean():.1f}; [{time.time()-t0:.1f}s]', flush=True)
best_seq = []
for rs in range(restarts):
    cov = np.zeros(len(R), np.float32)
    opp_ok = np.ones(nc, bool); seq = []
    while True:
        sat = (cov >= 2).astype(np.float32)
        feas = opp_ok & ((NRf @ sat) == 0)
        if seq: feas[seq] = False
        ids = np.nonzero(feas)[0]
        if len(ids) == 0: break
        # least overlap with current coverage (sum of coverage over N(x)) with random tie-breaking
        sc = NRf[ids] @ cov + rng.random(len(ids)) * 2.0
        c = int(ids[np.argmin(sc)])
        seq.append(c); cov += NRf[c]
        bc = H.Bmat(cand, cand[c:c + 1])[:, 0]
        opp_ok &= (bc != 0)
    if len(seq) > len(best_seq): best_seq = seq
    print(f'restart {rs}: size {len(seq)} (best {len(best_seq)}) [{time.time()-t0:.0f}s]', flush=True)
np.save(out, cand[np.array(best_seq, dtype=np.int64)])
print('saved', out, 'size', len(best_seq))
