#!/usr/bin/env python3
"""Card c2 (squad round 6): orbit graph of the cyclic subgroup <g> with g = h^k (h = a b^2, order 15), warm-started
with the 756 clique, then wclq2 (exact B&B for TEXACT CPU s, tabu local search for THEUR CPU s).
usage: run_sub.py K TEXACT THEUR SEED TAG [--init PATH]
Writes work/TAG.bin, work/TAG_s<seed>.clq (removed), gens/TAG.txt; prints the verified weight; if it beats the
best so far (best_weight.txt in c2) saves best_idx.txt and best_gen.txt in c2."""
import argparse
import os
import subprocess
import sys
import time

import numpy as np

from common import HERE, L, MPOW, MMUL, h_matrix, read_points, write_gens, orbit_graph

WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
GENS = os.path.join(HERE, 'gens')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('k', type=int)
    ap.add_argument('texact', type=float)
    ap.add_argument('theur', type=float)
    ap.add_argument('seed', type=int)
    ap.add_argument('tag')
    ap.add_argument('--init', default=os.path.join(HERE, '..', '..', 'd13D7_r4', 'c1', 'best_idx.txt'))
    ap.add_argument('--gen', default=None, help='optional explicit generator matrix file instead of h^k')
    args = ap.parse_args()
    t0 = time.time()
    os.makedirs(WORK, exist_ok=True)
    os.makedirs(GENS, exist_ok=True)
    if args.gen:
        from common import read_gens
        _, (g,) = read_gens(args.gen)
        desc = f'explicit generator from {args.gen}'
    else:
        h = h_matrix()
        g = MPOW(h, args.k)
        desc = f'cyclic subgroup <h^{args.k}>, h = a b^2 (order 15)'
    og = L.order_of(g)
    assert L.is_isom(g)
    print(f'{args.tag}: {desc}; element order {og}', flush=True)
    write_gens(os.path.join(GENS, f'{args.tag}.txt'), desc, [g])
    pts = read_points(args.init)
    lab, sizes, rep, good, init_path, init_w = orbit_graph(g, pts, args.tag, WORK)
    K = int(good.size)
    print(f'orbits {sizes.size}, good K={K}, warm weight {init_w} ({time.time() - t0:.1f}s)', flush=True)
    rows = L.compat_packed(lab, rep, good)
    w = sizes[good]
    gbin = os.path.join(WORK, f'{args.tag}.bin')
    L.write_graph_packed(gbin, rows, w)
    print(f'graph written, density {L.packed_density(rows):.4f} ({time.time() - t0:.1f}s)', flush=True)
    del rows
    out = os.path.join(WORK, f'{args.tag}_s{args.seed}.clq')
    cmd = [WCLQ, gbin, str(args.texact), str(args.theur), str(args.seed), out]
    if init_path:
        cmd.append(init_path)
    t1 = time.time()
    res = subprocess.run(cmd, capture_output=True, text=True)
    weight, opt, verts = L.read_clique(out)
    chosen = good[np.array(verts, dtype=np.int64)]
    idx = np.flatnonzero(np.isin(lab, chosen))
    ok = idx.size == weight and L.pairwise_ok(idx)
    err = [l for l in res.stderr.splitlines() if l.strip()]
    print(f'RESULT weight {weight} optimal {opt} verified {ok} wall {time.time() - t1:.1f}s | {"; ".join(err[-4:])}',
          flush=True)
    os.remove(out)
    os.remove(gbin)
    if ok:
        dst = os.path.join(WORK, f'{args.tag}_best.idx')
        with open(dst, 'w') as f:
            f.write(f'# {weight} points, {args.tag} (verified pairwise opposite)\n'
                    + '\n'.join(map(str, np.sort(idx).tolist())) + '\n')
        print(f'saved {dst}', flush=True)
    print(f'total wall {time.time() - t0:.1f}s', flush=True)


if __name__ == '__main__':
    main()
