# c3: orbit-union search for a cyclic group <h> (h from elems_seed1.npz). Orbits = cycles of h. Independent orbits are
# the nodes; two orbits are compatible iff all their cross pairs are non-orthogonal. Max clique in the compatibility
# graph (all weights equal) by an iterated local search (add / (1,1)-swap / perturbation with tabu).
# Usage: clique_ls.py ELEMS.npz KEY SECONDS SEED OUTPREFIX
import sys, time, numpy as np
from orth import *

def compat_full(cyc, ind):
    reps = np.array([cyc[o][0] for o in ind], dtype=np.int64)
    order = np.concatenate([np.array(c, dtype=np.int64) for c in cyc])
    sizes = [len(c) for c in cyc]
    starts = np.concatenate([[0], np.cumsum(sizes)[:-1]]).astype(np.int64)
    out = np.zeros((len(ind), len(cyc)), dtype=bool)
    for s in range(0, len(ind), 256):
        R = reps[s:s + 256]
        Zb = (Bm(U[R], U) == 0)
        cnt = np.add.reduceat(Zb[:, order], starts, axis=1)
        out[s:s + 256] = (cnt == 0)
    return out[:, ind]

def clique_ils(A, secs, seed):
    rng = np.random.default_rng(seed)
    n = A.shape[0]; nA = ~A; np.fill_diagonal(nA, False)
    inC = np.zeros(n, bool); miss = np.zeros(n, np.int64); tabu = np.zeros(n, np.int64)
    C = []; best = []; it = 0; t0 = time.time()
    def add(v):
        inC[v] = True; C.append(v); miss[:] += nA[:, v]
    def rem(v):
        inC[v] = False; C.remove(v); miss[:] -= nA[:, v]
    while time.time() - t0 < secs:
        it += 1
        free = np.flatnonzero((~inC) & (miss == 0) & (tabu < it))
        if free.size:
            add(int(free[rng.integers(free.size)]))
            if len(C) > len(best): best = list(C)
            continue
        sw = np.flatnonzero((~inC) & (miss == 1) & (tabu < it))
        if sw.size and rng.random() < 0.97:
            v = int(sw[rng.integers(sw.size)])
            u = int(np.flatnonzero(nA[v] & inC)[0])
            rem(u); add(v); tabu[u] = it + 7 + int(rng.integers(10))
        else:
            v = int(rng.integers(n))
            if inC[v]: continue
            for u in list(np.flatnonzero(nA[v] & inC)): rem(int(u)); tabu[int(u)] = it + 7
            add(v)
    return best, it

if __name__ == '__main__':
    Z = np.load(sys.argv[1]); key = sys.argv[2]; secs = float(sys.argv[3]); seed = int(sys.argv[4]); outp = sys.argv[5]
    perm = Z[key]; cyc = cycles(perm)
    ind = indep_orbits(cyc)
    t0 = time.time(); comp = compat_full(cyc, ind)
    A = comp & comp.T
    dens = A.sum() / max(1, A.shape[0] * (A.shape[0] - 1))
    print(f"{key}: orbits {len(cyc)}, independent {len(ind)}, sizes {sorted(set(len(cyc[o]) for o in ind))}, "
          f"compat density {dens:.3f}, build {time.time()-t0:.1f}s", flush=True)
    best, it = clique_ils(A, secs, seed)
    S = []
    for a in best: S.extend(cyc[ind[a]])
    S = np.array(sorted(S), dtype=np.int64)
    ok = is_indep(S)
    print(f"{key} seed {seed}: best {len(best)} orbits = {len(S)} points, independent {ok}, iterations {it}", flush=True)
    np.save(outp + '.npy', S)
    with open(outp + '.flags', 'w') as f:
        for i in S: f.write(f"{pid[i]} {sline[i]}\n")
