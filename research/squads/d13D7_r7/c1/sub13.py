#!/usr/bin/env python3
"""Card c1 (squad round 7, job cell-13-7): warm-started tabu on the orbit graphs of the subgroups <h^k> of the order-30
group <h> that gave the 500 set (generator research/squads/d13D7_r4/c2/best500_gen.txt).  k = 1 is <h> itself.

The 500 set is a union of <h>-orbits, hence of <h^k>-orbits.  Those <h^k>-orbits are good (pairwise opposite inside)
and pairwise compatible, so they are a clique of the <h^k> orbit graph.  That clique warm-starts wclq2: exact search
cut at TEXACT CPU seconds, then its tabu local search for THEUR CPU seconds (both measured by clock() inside wclq2).

usage: sub13.py --k K [--texact T] [--theur T2] [--seed S] [--maxK 70000]
Writes runlog.jsonl (one line per run), and best_idx.txt / best_gen.txt / best_weight.txt when a run beats 500.
"""
import argparse
import gc
import json
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbq13 as L  # noqa: E402

R4C2 = '/home/user/degree-diameter/research/squads/d13D7_r4/c2'
H_GEN = os.path.join(R4C2, 'best500_gen.txt')
START_IDX = os.path.join(R4C2, 'best500_idx.txt')
WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
RUNLOG = os.path.join(HERE, 'runlog.jsonl')
BEST_IDX = os.path.join(HERE, 'best_idx.txt')
BEST_GEN = os.path.join(HERE, 'best_gen.txt')
BEST_W = os.path.join(HERE, 'best_weight.txt')
START_W = 500


def read_gens(path):
    blocks = []
    for line in open(path):
        if line.startswith('# generator'):
            blocks.append([])
        elif line.strip() and not line.startswith('#') and blocks:
            blocks[-1].append(list(map(int, line.split())))
    return [np.array(b, dtype=np.int64) for b in blocks]


def density_sample(rows, rng, n=200):
    """edge density of the packed graph, from n sampled rows (keeps memory small)."""
    K = rows.shape[0]
    idx = rng.integers(0, K, min(n, K))
    bits = np.unpackbits(rows[idx].view(np.uint8), axis=1, bitorder='little')
    return float(bits[:, :K].sum()) / (len(idx) * max(1, K - 1))


def log(rec):
    with open(RUNLOG, 'a') as f:
        f.write(json.dumps(rec) + '\n')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--k', type=int, required=True)
    ap.add_argument('--texact', type=float, default=5.0)
    ap.add_argument('--theur', type=float, default=120.0)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--maxK', type=int, default=70000)
    ap.add_argument('--start', default=None, help='warm-start point file (default: the 500 set)')
    args = ap.parse_args()
    os.makedirs(WORK, exist_ok=True)
    (h,) = read_gens(H_GEN)
    assert L.order_of(h) == 30
    g = L.mpow(h, args.k)
    d = L.order_of(g)
    tag = f'k{args.k}'
    rec = dict(tag=tag, k=args.k, order=int(d), seed=args.seed, texact=args.texact, theur=args.theur)
    t0 = time.time()
    lab = L.orbit_labels([L.perm_of(g)])
    sizes, rep, good = L.analyse(lab)
    K = int(good.size)
    rec.update(norbits=int(sizes.size), K=K)
    print(f'{tag}: order {d}, orbits {sizes.size}, good K={K} ({time.time() - t0:.1f}s)', flush=True)
    pts = np.loadtxt(args.start or START_IDX, comments='#', dtype=np.int64).reshape(-1)
    pos = np.full(sizes.size, -1, np.int64)
    pos[good] = np.arange(K)
    labs = np.unique(lab[pts])
    gi = pos[labs]
    union = np.flatnonzero(np.isin(lab, labs))
    is_union = union.size == pts.size and np.array_equal(np.sort(union), np.sort(pts))
    rec.update(start_points=int(pts.size), start_orbits=int(labs.size), start_is_union=bool(is_union))
    if not (is_union and np.all(gi >= 0)):
        rec.update(weight=0, skipped='start set is not a union of good orbits')
        log(rec)
        print(rec, flush=True)
        return
    w = sizes[good]
    rec['start_weight'] = int(w[gi].sum())
    if K > args.maxK:
        rec.update(weight=0, skipped=f'K={K} > maxK={args.maxK}: adjacency needs {2 * K * ((K + 63) // 64) * 8 / 1e9:.2f} GB')
        log(rec)
        print(rec, flush=True)
        return
    rows = L.compat_packed(lab, rep, good)
    rec['density'] = round(density_sample(rows, np.random.default_rng(0)), 4)
    print(f'compat graph built ({time.time() - t0:.1f}s), density ~{rec["density"]}', flush=True)
    gbin = os.path.join(WORK, f'{tag}.bin')
    ginit = os.path.join(WORK, f'{tag}_init.txt')
    gclq = os.path.join(WORK, f'{tag}_s{args.seed}.clq')
    L.write_graph_packed(gbin, rows, w)
    del rows
    gc.collect()
    with open(ginit, 'w') as f:
        f.write('\n'.join(map(str, gi.tolist())) + '\n')
    cmd = [WCLQ, gbin, str(args.texact), str(args.theur), str(args.seed), gclq, ginit]
    t1 = time.time()
    res = subprocess.run(cmd, capture_output=True, text=True)
    err = [x for x in res.stderr.splitlines() if x.strip()]
    rec['wclq_stderr'] = err[-3:]
    rec['wclq_wall'] = round(time.time() - t1, 1)
    weight, opt, verts = L.read_clique(gclq)
    chosen = good[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    idx = np.flatnonzero(np.isin(lab, chosen))
    ok = bool(idx.size == weight and L.pairwise_ok(idx))
    rec.update(weight=int(weight), optimal=bool(opt), valid=ok)
    for fp in (gbin, gclq, ginit):
        if os.path.exists(fp):
            os.remove(fp)
    if ok and weight > rec['start_weight']:
        out_idx = os.path.join(WORK, f'{tag}_s{args.seed}_best.idx')
        with open(out_idx, 'w') as f:
            f.write(f'# {weight} points, pairwise opposite (wclq2 + numpy); subgroup <h^{args.k}> of order {d}\n')
            f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
        rec['idx_file'] = out_idx
    log(rec)
    print(f'RUN {tag} seed {args.seed}: weight {weight} (start {rec["start_weight"]}) K={K} optimal={opt} valid={ok} '
          f'wall {time.time() - t0:.1f}s; {"; ".join(err[-2:])}', flush=True)


if __name__ == '__main__':
    main()
