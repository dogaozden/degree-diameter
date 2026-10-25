#!/usr/bin/env python3
"""Card c1 (round 7), coordinator redirect: warm-started exact/tabu search on the orbit graphs of cyclic subgroups <x>
of the monomial group G (order 1296; generators research/squads/d13D7_r7/c3/best_gen.txt).  The 792 set of card c3 is a
union of G-orbits, hence of <x>-orbits, so it is a clique of the <x> orbit graph (warm start for wclq2).
usage: sub1296.py --orders 72,36,54 [--maxsub 1] [--texact 8] [--theur 40] [--seed 1]
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

C3 = '/home/user/degree-diameter/research/squads/d13D7_r7/c3'
G_GEN = os.path.join(C3, 'best_gen.txt')
START_IDX = os.path.join(C3, 'best_idx.txt')
WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
RUNLOG = os.path.join(HERE, 'runlog1296.jsonl')


def read_gens(path):
    blocks = []
    for line in open(path):
        if line.startswith('# generator'):
            blocks.append([])
        elif line.strip() and not line.startswith('#') and blocks:
            blocks[-1].append(list(map(int, line.split())))
    return [np.array(b, dtype=np.int64) for b in blocks]


def closure(gens):
    I = np.eye(7, dtype=np.int64)
    seen = {I.tobytes(): I}
    frontier = [I]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = L.mmul(x, g)
                k = y.tobytes()
                if k not in seen:
                    seen[k] = y
                    nxt.append(y)
        frontier = nxt
    return list(seen.values())


def cyc_powers(x):
    I = np.eye(7, dtype=np.int64)
    out, y = [], I.copy()
    while True:
        out.append(y.tobytes())
        y = L.mmul(y, x)
        if np.array_equal(y, I):
            break
    return frozenset(out)


def union_check(lab, pts):
    labs = np.unique(lab[pts])
    union = np.flatnonzero(np.isin(lab, labs))
    return bool(union.size == pts.size and np.array_equal(np.sort(union), np.sort(pts))), labs


def log(rec):
    with open(RUNLOG, 'a') as f:
        f.write(json.dumps(rec) + '\n')


def run_sub(gens_h, d, args, pts):
    tag = f'h{d}_s{args.seed}_{len(os.listdir(WORK))}'
    t0 = time.time()
    lab = L.orbit_labels([L.perm_of(g) for g in gens_h])
    sizes, rep, good = L.analyse(lab)
    K = int(good.size)
    rec = dict(tag=tag, order=d, norbits=int(sizes.size), K=K, seed=args.seed, texact=args.texact, theur=args.theur)
    ok_u, labs = union_check(lab, pts)
    pos = np.full(sizes.size, -1, np.int64)
    pos[good] = np.arange(K)
    gi = pos[labs]
    rec['start_is_union'] = ok_u
    if not ok_u or np.any(gi < 0):
        rec.update(weight=0, skipped='start set is not a union of good orbits')
        log(rec)
        print(rec, flush=True)
        return rec
    w = sizes[good]
    start_w = int(w[gi].sum())
    rec['start_weight'] = start_w
    if K > 40000:
        rec.update(weight=0, skipped=f'K={K} too large')
        log(rec)
        return rec
    rows = L.compat_packed(lab, rep, good)
    gbin = os.path.join(WORK, f'{tag}.bin')
    ginit = os.path.join(WORK, f'{tag}_init.txt')
    gclq = os.path.join(WORK, f'{tag}.clq')
    L.write_graph_packed(gbin, rows, w)
    del rows
    gc.collect()
    with open(ginit, 'w') as f:
        f.write('\n'.join(map(str, gi.tolist())) + '\n')
    print(f'{tag}: order {d}, orbits {sizes.size}, good K={K}, start weight {start_w} '
          f'({time.time() - t0:.1f}s), running wclq2', flush=True)
    res = subprocess.run([WCLQ, gbin, str(args.texact), str(args.theur), str(args.seed), gclq, ginit],
                         capture_output=True, text=True)
    err = [s for s in res.stderr.splitlines() if s.strip()]
    weight, opt, verts = L.read_clique(gclq)
    chosen = good[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    idx = np.flatnonzero(np.isin(lab, chosen))
    ok = bool(idx.size == weight and L.pairwise_ok(idx))
    rec.update(weight=int(weight), optimal=bool(opt), valid=ok, wclq_stderr=err[-3:])
    for fp in (gbin, gclq, ginit):
        if os.path.exists(fp):
            os.remove(fp)
    if ok and weight > start_w:
        p = os.path.join(WORK, f'{tag}_best.idx')
        with open(p, 'w') as f:
            f.write(f'# {weight} points, pairwise opposite (wclq2 + numpy); cyclic subgroup of order {d} of G\n')
            f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
        rec['idx_file'] = p
    rec['t_wall'] = round(time.time() - t0, 1)
    log(rec)
    print(f'RUN {tag}: weight {weight} (start {start_w}) K={K} optimal={opt} valid={ok} wall {rec["t_wall"]}s; '
          f'{"; ".join(err[-2:])}', flush=True)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--orders', default='72,36,54')
    ap.add_argument('--maxsub', type=int, default=1)
    ap.add_argument('--texact', type=float, default=8.0)
    ap.add_argument('--theur', type=float, default=40.0)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--pairs', type=int, default=400)
    args = ap.parse_args()
    os.makedirs(WORK, exist_ok=True)
    gens = read_gens(G_GEN)
    assert len(gens) == 2 and all(L.is_isom(g) for g in gens)
    G = closure(gens)
    pts = np.loadtxt(START_IDX, comments='#', dtype=np.int64).reshape(-1)
    labG = L.orbit_labels([L.perm_of(g) for g in gens])
    okG, labsG = union_check(labG, pts)
    print(f'|G| = {len(G)}; start set {pts.size} points; union of G-orbits: {okG} ({labsG.size} orbits)', flush=True)
    rng = np.random.default_rng(args.seed)
    found = {}
    for x in G:
        key = cyc_powers(x)
        if len(key) in (9, 18, 6, 3) and key not in found:
            found[key] = (len(key), [x])
    for _ in range(args.pairs):
        x = G[rng.integers(len(G))]
        y = G[rng.integers(len(G))]
        H = closure([x, y])
        key = frozenset(m.tobytes() for m in H)
        if key not in found:
            found[key] = (len(H), [x, y])
    sizes = sorted(v[0] for v in found.values())
    import collections
    print('subgroups found by order:', sorted(collections.Counter(sizes).items()), flush=True)
    for d_str in args.orders.split(','):
        d = int(d_str)
        cand = [v for v in found.values() if v[0] == d]
        print(f'order {d}: {len(cand)} subgroups, using {min(len(cand), args.maxsub)}', flush=True)
        for _, gs in cand[:args.maxsub]:
            run_sub(gs, d, args, pts)


if __name__ == '__main__':
    main()
