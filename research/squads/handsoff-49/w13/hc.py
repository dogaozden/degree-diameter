"""Hill climb / annealing on S (|S|=4, e in S) for Haar graph H(G,S) of a metacyclic group.
cost = |G \\ (S^-1 S)^4| + |G \\ (S S^-1)^4|  (same-side far elements of the two roots; 0 iff diameter <= 9)."""
import sys, time, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/handsoff-49/w13')
from meta import *

def cost_fn(T, Sinv, S, reps=4):
    S = np.asarray(S)
    N = T.shape[0]
    TA = prodset(T, Sinv[S], S)          # S^-1 S
    TB = prodset(T, S, Sinv[S])          # S S^-1
    PA = np.array([0]); PB = np.array([0])
    for _ in range(reps):
        PA = prodset(T, PA, TA); PB = prodset(T, PB, TB)
    fa = N - len(PA); fb = N - len(PB)
    return fa + fb, fa, fb

def anneal(T, Sinv, seed, secs, init=None, temp0=1.0):
    rng = np.random.default_rng(seed)
    N = T.shape[0]
    S = list(init) if init is not None else [0] + list(rng.choice(np.arange(1, N), 3, replace=False))
    c, fa, fb = cost_fn(T, Sinv, S)
    best = (c, list(S))
    t0 = time.time(); it = 0
    while time.time() - t0 < secs:
        it += 1
        i = rng.integers(1, 4)
        x = int(rng.integers(1, N))
        if x in S: continue
        S2 = list(S); S2[i] = x
        c2, _, _ = cost_fn(T, Sinv, S2)
        temp = temp0 * max(0.05, 1 - (time.time() - t0) / secs)
        if c2 <= c or rng.random() < np.exp(-(c2 - c) / max(temp, 1e-3)):
            S, c = S2, c2
            if c < best[0]:
                best = (c, list(S))
    return best, it

if __name__ == "__main__":
    m, k, r = map(int, sys.argv[1:4]); secs = float(sys.argv[4]); seed = int(sys.argv[5])
    T = meta_table(m, k, r); Sinv = inverses(T)
    best, it = anneal(T, Sinv, seed, secs)
    print("m k r", m, k, r, "best cost", best[0], "S", best[1], "iters", it, flush=True)
