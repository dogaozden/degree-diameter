#!/usr/bin/env python3
"""Card c3 (squad round 6): re-solve one saved group (gens file) with a longer local search.

usage: relong6.py GENSFILE TEXACT THEUR SEED
Rebuilds the orbit graph of the group, runs wclq2 (exact search for TEXACT CPU s, then tabu local search for THEUR s),
verifies the union with numpy, and writes best_idx.txt / best_gen.txt when it beats the best saved so far."""
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L  # noqa: E402
import compat6 as C6  # noqa: E402


def read_gens(path):
    blocks, desc = [], ''
    for line in open(path):
        if line.startswith('# generator'):
            blocks.append([])
        elif line.startswith('#'):
            desc = line[1:].strip()
        elif line.strip() and blocks:
            blocks[-1].append(list(map(int, line.split())))
    return desc, [np.array(b, dtype=np.int64) for b in blocks]


def main():
    gpath, texact, theur, seed = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
    desc, gens = read_gens(gpath)
    t0 = time.process_time()
    lab = L.orbit_labels([L.perm_of(g) for g in gens])
    sizes, rep, good = L.analyse(lab)
    K = int(good.size)
    rows = C6.compat_rows(lab, rep, good)
    w = sizes[good]
    tag = os.path.splitext(os.path.basename(gpath))[0]
    gbin = os.path.join(HERE, 'work', f'{tag}_long.bin')
    gclq = os.path.join(HERE, 'work', f'{tag}_long_s{seed}.clq')
    L.write_graph_packed(gbin, rows, w)
    print(f'{desc}: K={K} good orbits, graph built in {time.process_time() - t0:.1f}s', flush=True)
    res = subprocess.run([os.path.join(HERE, 'wclq2'), gbin, str(texact), str(theur), str(seed), gclq],
                         capture_output=True, text=True, timeout=texact + theur + 300)
    print('solver:', res.stdout.strip(), '|', ' / '.join(res.stderr.strip().splitlines()[-2:]), flush=True)
    weight, opt, verts = L.read_clique(gclq)
    chosen = good[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    idx = np.flatnonzero(np.isin(lab, chosen))
    ok = idx.size == weight and L.pairwise_ok(idx)
    print(f'RESULT weight={weight} optimal={bool(opt)} verified={ok} cpu_total={time.process_time() - t0:.1f}s',
          flush=True)
    if ok:
        prev = 0
        if os.path.exists(os.path.join(HERE, 'best_weight.txt')):
            prev = int(open(os.path.join(HERE, 'best_weight.txt')).read().strip() or 0)
        if weight > prev:
            with open(os.path.join(HERE, 'best_idx.txt'), 'w') as f:
                f.write(f'# {weight} points, pairwise opposite (verified by wclq2 + numpy); generators in best_gen.txt\n')
                f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
            with open(os.path.join(HERE, 'best_gen.txt'), 'w') as f:
                f.write(f'# {weight} points: {desc}\n')
                for i, g in enumerate(gens):
                    f.write(f'# generator {i}\n')
                    f.write(L.mat_to_text(g))
            with open(os.path.join(HERE, 'best_weight.txt'), 'w') as f:
                f.write(f'{weight}\n')
            print('NEW BEST', weight, flush=True)
    for fp_ in (gbin, gclq):
        if os.path.exists(fp_):
            os.remove(fp_)


if __name__ == '__main__':
    main()
