#!/usr/bin/env python3
"""c7 (wildcard A): isometric copies of the base set R756.  For each seed, g = ovlib.random_isometry(q=11, nref=8)
is an isometry of Q(6,11) (standard form x0x4+x1x5+x2x6-x3^2, polar Gram ovlib.std_gram); the image g(R756) is
mapped back to hexgen point indices with Hex.index_of.  Checks: g is an isometry, the image lies on the quadric,
has 756 distinct points, is pairwise opposite (B != 0), and reports the candidate pool (points of H(11) not
collinear with the image; always 76,608 for a pairwise-opposite 756-set).  Writes OUT/R_iso<seed>.npy (int64).
usage: iso_base.py OUT SEED [SEED ...]"""
import numpy as np, sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ovlib
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
out = sys.argv[1]; os.makedirs(out, exist_ok=True)
H = Hex(SP + 'hex_q11.bin'); q = H.q; N = H.N
R0 = np.load(SP + 'R756idx.npy').astype(np.int64)
G = ovlib.std_gram(q)
X0 = H.X[R0].astype(np.int64)
assert (H.index_of(X0) == R0).all(), 'index_of does not invert the coordinate map'
Qv = (X0[:, 0] * X0[:, 4] + X0[:, 1] * X0[:, 5] + X0[:, 2] * X0[:, 6] - X0[:, 3] ** 2) % q
assert (Qv == 0).all()
for seed in map(int, sys.argv[2:]):
    M = ovlib.random_isometry(q=q, nref=8, rng=random.Random(seed))
    assert ovlib.is_isometry(M, G, q), 'not an isometry'
    Y = (X0 @ np.array(M, dtype=np.int64).T) % q          # M acts on column vectors: y = M x
    idx = H.index_of(Y).astype(np.int64)                    # KeyError if a coordinate is not a point of Q(6,11)
    assert len(set(idx.tolist())) == len(R0), 'image is not 756 distinct points'
    Bm = H.Bmat(idx, idx); np.fill_diagonal(Bm, 1)
    assert (Bm != 0).all(), 'image is not pairwise opposite'
    colR = np.zeros(N, bool); colR[H.lp[H.pl[idx]].reshape(-1)] = True; colR[idx] = True
    fn = os.path.join(out, f'R_iso{seed}.npy'); np.save(fn, idx)
    print(f'seed {seed}: {fn}  candidates {int((~colR).sum())}  overlap with R756 {len(set(idx.tolist()) & set(R0.tolist()))}'
          f'  M[0]={M[0]}', flush=True)
