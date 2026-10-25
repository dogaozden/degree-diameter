#!/usr/bin/env python3
"""replay8.py (card c1, squad round 5): rebuild the orbit graph of a saved group (gens file written by run8.py), run the
clique solver (wclq2) for longer, optionally warm-started from a point-index file (a union of orbits of this group, or
any pairwise-opposite set whose orbits are good), and write the best union as point indices.
usage: replay8.py GENS_FILE TEXACT THEUR SEED OUT_PREFIX [INIT_IDX_FILE]
"""
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orb8 as L  # noqa: E402
import run8 as R  # noqa: E402


def read_idx(path):
    return [int(x) for x in open(path) if x.strip() and not x.startswith('#')]


def main():
    gens_file, texact, theur, seed, out = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    init_file = sys.argv[6] if len(sys.argv) > 6 else None
    desc, gens = L.read_gens(gens_file)
    lab, sizes, rep, good, fp = R.analyse_group(gens)
    K = int(good.size)
    rows = L.compat_packed(lab, rep, good)
    w = sizes[good]
    os.makedirs(R.WORK, exist_ok=True)
    gbin = os.path.join(R.WORK, f'rp_{fp}_{seed}.bin')
    gclq = os.path.join(R.WORK, f'rp_{fp}_{seed}.clq')
    L.write_graph_packed(gbin, rows, w)
    cmd = [R.WCLQ, gbin, str(texact), str(theur), str(seed), gclq]
    init_path = None
    if init_file:
        pos = np.full(sizes.size, -1, np.int64)
        pos[good] = np.arange(K)
        pts = read_idx(init_file)
        orbs = np.unique(lab[np.array(pts, dtype=np.int64)])
        gi = pos[orbs]
        if np.all(gi >= 0):
            init_path = gclq + '.init'
            with open(init_path, 'w') as f:
                f.write('\n'.join(map(str, gi.tolist())) + '\n')
            cmd.append(init_path)
        else:
            print('init file has orbits that are not good in this group; running without warm start')
    res = subprocess.run(cmd, capture_output=True, text=True, timeout=texact + theur + 300)
    print(res.stderr.strip())
    weight, opt, verts = L.read_clique(gclq)
    chosen = good[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    idx = np.flatnonzero(np.isin(lab, chosen))
    ok = idx.size == weight and L.pairwise_ok(idx)
    print(f'RESULT weight {weight} K {K} optimal {opt} verified {ok} group {desc}')
    if ok:
        with open(out + '_idx.txt', 'w') as f:
            f.write(f'# {weight} points, pairwise opposite (replay of {os.path.basename(gens_file)})\n')
            f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
        with open(out + '_gen.txt', 'w') as f:
            f.write(f'# {weight} points: {desc}\n')
            for i, g in enumerate(gens):
                f.write(f'# generator {i}\n')
                f.write(L.mat_to_text(g))
    for p in (gbin, gclq, init_path):
        if p and os.path.exists(p):
            os.remove(p)


if __name__ == '__main__':
    main()
