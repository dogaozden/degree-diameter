#!/usr/bin/env python3
"""Card c4 (squad round 4): exact deficit test for every union T of S-orbits with fmin <= freed(T) <= fmax.
For T: F = freed outside points (all S-blockers inside the removed orbits T).  A gain is a pairwise-opposite A subset of F
with |A| > |N_S(A)| (N_S = S points blocking some point of A); then (S minus N_S(A)) plus A is pairwise opposite, size 720 + gain.
Branch and bound per T with a node limit; reports the best gain and any T with gain > 0.
usage: deficit2.py FMIN FMAX NODELIMIT [CPU_LIMIT_SECONDS]"""
import sys, os, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L

fmin, fmax, nodelim = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
cpulim = float(sys.argv[4]) if len(sys.argv) > 4 else 500.0
S = np.loadtxt(os.path.join(HERE, 'init720_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
sig = np.load(os.path.join(HERE, 'sig720.npy'))
f = np.load(os.path.join(HERE, 'freed_T.npy'))
K = 16
PJ = L.PJ; P = L.P; N = L.N
inS = np.zeros(N, bool); inS[S] = True
# blocker bitmask per outside point over S positions (python ints)
Bmask = np.zeros(N, dtype=object)
Bl = [0] * N
for i, s in enumerate(S.tolist()):
    z = ((PJ @ P[s]) % 11) == 0
    z[s] = False
    for y in np.flatnonzero(z).tolist():
        Bl[y] |= (1 << i)
Ts = [t for t in range(1, 1 << K) if fmin <= f[t] <= fmax]
print('T count', len(Ts), flush=True)
t0 = time.time()
gains = {}
hits = 0; maxval = -10**9; arg = None; done = 0
for t in Ts:
    if time.process_time() - t0 > cpulim:
        print('CPU limit reached after', done, 'T', flush=True); break
    F = np.flatnonzero((sig > 0) & ((sig & ~t) == 0) & (~inS))
    n = F.size
    M = (PJ[F] @ P[F].T) % 11
    comp = M != 0
    np.fill_diagonal(comp, False)
    bl = [Bl[y] for y in F.tolist()]
    adj = [int(sum(1 << j for j in np.flatnonzero(comp[i]).tolist())) for i in range(n)]
    best = [0, None]; nodes = [0]; trunc = [False]
    def pc(x):
        return x.bit_count()
    def rec(A, Nmask, cand):      # cand: bitmask of candidate indices (pairwise compatible with all of A)
        nodes[0] += 1
        if nodes[0] > nodelim:
            trunc[0] = True; return
        val = len(A) - pc(Nmask)
        if val > best[0]:
            best[0] = val; best[1] = list(A)
        c = cand
        while c:
            if len(A) + pc(c) - pc(Nmask) <= best[0]:
                return
            low = c & -c
            j = low.bit_length() - 1
            c ^= low
            A.append(j)
            rec(A, Nmask | bl[j], c & adj[j])
            A.pop()
            if trunc[0]:
                return
    full = (1 << n) - 1
    rec([], 0, full)
    done += 1
    if best[0] > 0:
        print('GAIN T', t, 'orbits', [i for i in range(K) if t >> i & 1], 'gain', best[0], 'A', [int(F[j]) for j in best[1]], flush=True)
    if trunc[0]:
        hits += 1
    if best[0] > maxval:
        maxval = best[0]; arg = t
print('done', done, 'T in %.1fs' % (time.time() - t0), '| best gain %d at T=%s | node-limit hits %d' % (maxval, arg, hits), flush=True)
