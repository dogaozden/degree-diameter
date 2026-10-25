#!/usr/bin/env python3
"""Card c4 (squad round 4): exact refill test for every union T of S-orbits.
Removing T from S and refilling with a pairwise-opposite set A of freed points (sig(a) subset of T) gives
|S| - |T| + |A| - |N_T(A)| ... i.e. the gain is |A| - |N_S(A)| where N_S(A) = the S points blocking some a in A.
A gain > 0 is found by branch and bound over the freed points F(T) (maximising |A| - |N(A)| over pairwise opposite A)."""
import sys, os, time
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L

S = np.loadtxt(os.path.join(HERE, 'init720_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
lab = np.load(os.path.join(HERE, 'lab720.npy'))
labs_S = np.load(os.path.join(HERE, 'labs_S720.npy'))
sig = np.load(os.path.join(HERE, 'sig720.npy'))
f = np.load(os.path.join(HERE, 'freed_T.npy'))
K = labs_S.size
PJ = L.PJ; P = L.P
N = L.N
# blocker bitmasks (over S positions) for all outside points
spos = {int(s): i for i, s in enumerate(S.tolist())}
Bl = [0] * N
cntS = np.zeros(N, np.int64)
for i, s in enumerate(S.tolist()):
    z = ((PJ @ P[s]) % 11) == 0
    z[s] = False
    cntS += z
    idx = np.flatnonzero(z)
    for y in idx.tolist():
        Bl[y] |= (1 << i)
inS = np.zeros(N, bool); inS[S] = True
print('blocker counts of outside points: min', cntS[~inS].min(), 'max', cntS[~inS].max(), flush=True)
# opposition among outside points is needed only inside F(T); B(a,b) != 0 via PJ
def opp(a, b):
    return ((PJ[a] @ P[b]) % 11) != 0

def best_deficit(F, limit_nodes=2000000):
    """max over pairwise opposite A subset of F of |A| - |N(A)| (N = union of blocker bitmasks); returns (best, A)."""
    n = len(F)
    if n == 0:
        return 0, []
    comp = [[False] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            comp[i][j] = comp[j][i] = opp(F[i], F[j])
    bl = [Bl[y] for y in F]
    best = [0, []]
    nodes = [0]
    def rec(i, A, Nmask, cand):
        nodes[0] += 1
        if nodes[0] > limit_nodes:
            return
        val = len(A) - bin(Nmask).count('1')
        if val > best[0]:
            best[0] = val; best[1] = list(A)
        # bound: each remaining candidate adds at most 1
        if len(A) + len(cand) - bin(Nmask).count('1') <= best[0]:
            return
        for k, j in enumerate(cand):
            # bound with candidates after k
            if len(A) + (len(cand) - k) - bin(Nmask).count('1') <= best[0]:
                return
            newcand = [t for t in cand[k + 1:] if comp[j][t]]
            A.append(j)
            rec(i, A, Nmask | bl[j], newcand)
            A.pop()
    rec(0, [], 0, [j for j in range(n)])
    return best[0], [F[j] for j in best[1]], nodes[0]

if __name__ == '__main__':
    fmax = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    Ts = [t for t in range(1, 1 << K) if 46 <= f[t] <= fmax]
    print('T with 46 <= freed <= %d: %d' % (fmax, len(Ts)), flush=True)
    t0 = time.time()
    bestgain = -999; bestT = None; nlim = 0
    for c, t in enumerate(Ts):
        F = np.flatnonzero((sig > 0) & ((sig & ~t) == 0) & (~inS)).tolist()
        if len(F) != f[t]:
            print('mismatch', t, len(F), f[t]); break
        res = best_deficit(F)
        val, A = res[0], res[1]
        if len(res) > 2 and res[2] >= 2000000: nlim += 1
        if val > bestgain:
            bestgain = val; bestT = (t, A)
        if val > 0:
            print('IMPROVEMENT candidate: T', t, 'gain', val, 'A', A, flush=True)
    print('done in %.1fs; max gain over these T: %d (T=%s); node-limit hits %d' % (time.time() - t0, bestgain, bestT[0] if bestT else None, nlim))
