# c3 final push: clique ILS on the orbit compatibility graph of one stored element, optional initial solution.
# Usage: clique_ls2.py ELEMS.npz KEY SECONDS SEED OUTPREFIX [INIT_POINTS_FILE]
import sys, time, numpy as np
from orth import *
from clique_ls import compat_full

def clique_ils_init(A, secs, seed, init):
    rng = np.random.default_rng(seed)
    n = A.shape[0]; nA = ~A; np.fill_diagonal(nA, False)
    inC = np.zeros(n, bool); miss = np.zeros(n, np.int64); tabu = np.zeros(n, np.int64)
    C = []; best = []; it = 0; t0 = time.time()
    def add(v):
        inC[v] = True; C.append(v); miss[:] += nA[:, v]
    def rem(v):
        inC[v] = False; C.remove(v); miss[:] -= nA[:, v]
    for v in init:
        if not inC[v] and miss[v] == 0: add(int(v))
    best = list(C)
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
    init_file = sys.argv[6] if len(sys.argv) > 6 else None
    perm = Z[key]; cyc = cycles(perm)
    ind = indep_orbits(cyc)
    comp = compat_full(cyc, ind); A = comp & comp.T
    dens = A.sum() / max(1, A.shape[0] * (A.shape[0] - 1))
    init = []
    if init_file:
        pts = set(int(x) for x in open(init_file).read().split())
        orb_of = {}
        for a, o in enumerate(ind):
            for pt in cyc[o]: orb_of[pt] = a
        init = sorted(set(orb_of[pt] for pt in pts if pt in orb_of))
        print(f"init: {len(init)} orbits from {len(pts)} points", flush=True)
    print(f"{key}: orbits {len(cyc)}, independent {len(ind)}, sizes {sorted(set(len(cyc[o]) for o in ind))}, density {dens:.3f}", flush=True)
    best, it = clique_ils_init(A, secs, seed, init)
    S = []
    for a in best: S.extend(cyc[ind[a]])
    S = np.array(sorted(S), dtype=np.int64)
    ok = is_indep(S)
    print(f"{key} seed {seed}: best {len(best)} orbits = {len(S)} points, independent {ok}, iterations {it}", flush=True)
    np.save(outp + '.npy', S)
    with open(outp + '.flags', 'w') as f:
        for i in S: f.write(f"{pid[i]} {sline[i]}\n")
