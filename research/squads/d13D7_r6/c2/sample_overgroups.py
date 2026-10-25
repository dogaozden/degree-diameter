#!/usr/bin/env python3
"""Card c2 (squad round 6): overgroups H = <h, g> of <h> with g in N(<h>) (sampled), exact/tabu max-weight clique on the
H-orbit graph of pairwise-opposite orbit unions.  usage: sample_overgroups.py M SEED TEXACT THEUR"""
import os
import subprocess
import sys
import time

import numpy as np

from common import HERE, L, MMUL, MPOW, h_matrix, read_points, write_gens

WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
p = 11


def pkey(g):
    a = (g % p).tobytes()
    b = ((-g) % p).tobytes()
    return min(a, b)


def main():
    M, seed, texact, theur = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4])
    t0 = time.time()
    d = np.load(os.path.join(HERE, 'norm_all.npz'))
    mats = d['mats']
    reps = {}
    for g in mats:
        reps.setdefault(pkey(g), g)
    projs = list(reps.values())
    print(f'N(<h>): {len(mats)} matrices, {len(projs)} projective elements', flush=True)
    rng = np.random.default_rng(seed)
    h = h_matrix()
    ph = L.perm_of(h)
    S = read_points(os.path.join(HERE, '..', '..', 'd13D7_r4', 'c1', 'best_idx.txt'))
    hp = {pkey(MPOW(h, k)) for k in range(15)}
    seen_fp = set()
    results = []
    order = rng.permutation(len(projs))
    tried = 0
    for t in order:
        if tried >= M:
            break
        g = projs[t]
        if pkey(g) in hp:
            continue
        tried += 1
        lab = L.orbit_labels([ph, L.perm_of(g)])
        sizes, rep, good = L.analyse(lab)
        K = int(good.size)
        fp = (hash(lab.tobytes()) if False else None)
        key = (tuple(sorted(np.bincount(lab).tolist())), K)
        if key in seen_fp:
            continue
        seen_fp.add(key)
        if K > 6000:
            print(f'skip: K={K} too big (orbits {sizes.size})', flush=True)
            continue
        labs = np.unique(lab[S])
        union = np.flatnonzero(np.isin(lab, labs))
        is_union = union.size == S.size and np.array_equal(np.sort(union), np.sort(S))
        pos = np.full(sizes.size, -1, np.int64)
        pos[good] = np.arange(K)
        init_path = None
        init_w = None
        if is_union:
            init_path = os.path.join(WORK, f'ov{seed}_{tried}_init.txt')
            with open(init_path, 'w') as f:
                f.write('\n'.join(map(str, pos[labs].tolist())) + '\n')
            init_w = int(sizes[labs].sum())
        rows = L.compat_packed(lab, rep, good)
        w = sizes[good]
        gbin = os.path.join(WORK, f'ov{seed}_{tried}.bin')
        L.write_graph_packed(gbin, rows, w)
        out = os.path.join(WORK, f'ov{seed}_{tried}.clq')
        cmd = [WCLQ, gbin, str(texact), str(theur), str(seed + tried), out]
        if init_path:
            cmd.append(init_path)
        res = subprocess.run(cmd, capture_output=True, text=True)
        weight, opt, verts = L.read_clique(out)
        chosen = good[np.array(verts, dtype=np.int64)]
        idx = np.flatnonzero(np.isin(lab, chosen))
        ok = idx.size == weight and L.pairwise_ok(idx)
        orbit_sz = sorted(set(sizes[np.unique(lab)].tolist()))
        line = (f'#{tried}: orbits {sizes.size}, K={K}, S-invariant {is_union}, weight {weight} optimal {opt} '
                f'verified {ok} (warm {init_w}) orbit sizes {orbit_sz}')
        print(line, flush=True)
        results.append((weight, opt, ok, K, is_union, orbit_sz, g))
        if ok and weight >= 756:
            with open(os.path.join(WORK, f'ov{seed}_{tried}_best.idx'), 'w') as f:
                f.write(f'# {weight} points overgroup sample {tried}\n' + '\n'.join(map(str, np.sort(idx).tolist())) + '\n')
            print("  *** weight >= 756 (saved)", flush=True)
            write_gens(os.path.join(HERE, "gens", f"ov{seed}_{tried}.txt"), "overgroup <h, g>", [g])
        for fpth in [gbin, out] + ([init_path] if init_path else []):
            if os.path.exists(fpth):
                os.remove(fpth)
    best = max(results, key=lambda r: r[0]) if results else None
    print('best overgroup weight:', best[0] if best else None, 'optimal' if best and best[1] else '', flush=True)
    print(f'total wall {time.time() - t0:.1f}s', flush=True)


if __name__ == '__main__':
    main()
