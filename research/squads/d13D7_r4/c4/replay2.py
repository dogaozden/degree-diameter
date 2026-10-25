#!/usr/bin/env python3
"""Card c3 (squad round 3): rebuild the orbit graph of a saved group (gens file) and re-solve its clique problem.

usage: replay2.py GENSFILE TEXACT THEUR SEED [--init POINTS] [--tag NAME] [--solver BIN]

GENSFILE: a file written by run_groups.py (or by hand): '# description' then '# generator i' blocks of 7x7 matrices.
--init POINTS: a point-index file (e.g. best_idx.txt); its points are mapped to orbit indices of this group and used
               as a warm-start clique (must be a union of orbits; otherwise it is reported and ignored).
Writes the verified best union to work/<tag>_best.idx (point indices) when it improves on the best of this run."""
import argparse
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L  # noqa: E402


def read_gens(path):
    desc, blocks = '', []
    for line in open(path):
        if line.startswith('# generator'):
            blocks.append([])
        elif line.startswith('#'):
            desc = line[1:].strip()
        elif line.strip() and blocks:
            blocks[-1].append(list(map(int, line.split())))
    return desc, [np.array(b, dtype=np.int64) for b in blocks]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('gens')
    ap.add_argument('texact', type=float)
    ap.add_argument('theur', type=float)
    ap.add_argument('seeds', type=int, nargs='+')
    ap.add_argument('--init', default=None)
    ap.add_argument('--tag', default=None)
    ap.add_argument('--solver', default=os.path.join(HERE, 'wclq2'))
    args = ap.parse_args()
    desc, gens = read_gens(args.gens)
    tag = args.tag or os.path.splitext(os.path.basename(args.gens))[0]
    work = os.path.join(HERE, 'work')
    os.makedirs(work, exist_ok=True)
    t = time.time()
    lab = L.orbit_labels([L.perm_of(g) for g in gens])
    sizes, rep, good = L.analyse(lab)
    K = int(good.size)
    print(f'{tag}: {desc}; orbits {sizes.size}, good orbits K={K} ({time.time() - t:.1f}s)', flush=True)
    rows = L.compat_packed(lab, rep, good)
    w = sizes[good]
    gbin = os.path.join(work, f'{tag}.bin')
    L.write_graph_packed(gbin, rows, w)
    print(f'graph written, density {L.packed_density(rows):.4f} ({time.time() - t:.1f}s)', flush=True)
    init_path = None
    init_w = None
    if args.init:
        pts = np.loadtxt(args.init, comments='#', dtype=np.int64).reshape(-1)
        labs = np.unique(lab[pts])
        pos = np.full(sizes.size, -1, np.int64)
        pos[good] = np.arange(K)
        gi = pos[labs]
        if np.any(gi < 0):
            print('init set uses a non-good orbit; ignored', flush=True)
        else:
            union = np.flatnonzero(np.isin(lab, labs))
            is_union = union.size == pts.size and np.array_equal(np.sort(union), np.sort(pts))
            print(f'init set: {pts.size} points = union of {labs.size} orbits: {is_union}', flush=True)
            init_path = os.path.join(work, f'{tag}_init.txt')
            with open(init_path, 'w') as f:
                f.write('\n'.join(map(str, gi.tolist())) + '\n')
            init_w = int(w[gi].sum())
    best = 0
    for s in args.seeds:
        out = os.path.join(work, f'{tag}_s{s}.clq')
        cmd = [args.solver, gbin, str(args.texact), str(args.theur), str(s), out]
        if init_path:
            cmd.append(init_path)
        t1 = time.time()
        res = subprocess.run(cmd, capture_output=True, text=True)
        weight, opt, verts = L.read_clique(out)
        chosen = good[np.array(verts, dtype=np.int64)]
        idx = np.flatnonzero(np.isin(lab, chosen))
        ok = idx.size == weight and L.pairwise_ok(idx)
        err = [l for l in res.stderr.splitlines() if l.strip()]
        print(f'seed {s}: weight {weight} optimal {opt} verified {ok} wall {time.time() - t1:.1f}s '
              f'| {"; ".join(err[-3:])}', flush=True)
        if ok and weight > best:
            best = weight
            with open(os.path.join(work, f'{tag}_best.idx'), 'w') as f:
                f.write(f'# {weight} points, {tag}\n' + '\n'.join(map(str, np.sort(idx).tolist())) + '\n')
        os.remove(out)
    if init_w is not None:
        print(f'warm-start weight was {init_w}', flush=True)
    os.remove(gbin)


if __name__ == '__main__':
    main()
