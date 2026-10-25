#!/usr/bin/env python3
"""run8.py (card c1, squad round 5): orbit-union search for pairwise-opposite point sets of H(8).

Port of research/squads/d13D7_r4/c3/run_q.py to GF(8) (library: orb8.py).  Modes:
  cyc  : cyclic groups <h>, h = g^(m/d), g a random isometry (product of k transvections), m = |g|, d | m, dmin<=d<=dmax.
  pair : commuting pairs <a'> x <b'>: a a product of transvections t_v, v in a non-degenerate U (dim 2 or 4),
         b a product of transvections t_w, w in U-perp (dim 5 or 3); a' = a^(|a|/da), b' = b^(|b|/db).
For every group: orbits, good orbits, compatibility, exact max-weight clique (wclq2: branch and bound for TEXACT CPU s,
tabu local search for THEUR s), numpy re-verification of the union.  Groups are deduplicated by orbit-structure
fingerprint.  Outputs in this folder: runlog8.jsonl, gens/<fp>.txt, work/, and when a union beats the best so far:
best_raw_idx.txt (point indices), best_raw_gen.txt (generators).
usage: run8.py --mode cyc|pair [--seed S] [--cpu SEC] [--dmin 5] [--dmax 600] [--kmax 8000] [--texact 3] [--theur 0.5]
CPU is the total of driver plus solver children; keep --cpu <= 600.
"""
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orb8 as L  # noqa: E402

WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
GENS = os.path.join(HERE, 'gens')
RUNLOG = os.path.join(HERE, 'runlog8.jsonl')
BEST_IDX = os.path.join(HERE, 'best_raw_idx.txt')
BEST_GEN = os.path.join(HERE, 'best_raw_gen.txt')


def cpu_total():
    t = os.times()
    return t.user + t.system + t.children_user + t.children_system


def cyc_samples(rng, dmin, dmax):
    while True:
        k = int(rng.integers(3, 13))
        g = L.rand_transv_in(rng, L.I7, k)
        m = L.order_of(g)
        ds = [d for d in L.divisors(m) if dmin <= d <= dmax and d > 1]
        for i in rng.permutation(len(ds)):
            d = ds[i]
            h = L.mpow(g, m // d)
            yield dict(mode='cyc', order=d, gens=[h], parent_order=m, nref=k,
                       desc=f'cyclic order {d}: h = g^({m // d}), g = product of {k} transvections, |g| = {m}')


def pair_samples(rng, dmin, dmax, ks, perk):
    tries = 0
    while True:
        tries += 1
        if tries > 100000:
            raise RuntimeError('no commuting pairs found')
        k = int(ks[rng.integers(0, len(ks))])
        E, F = L.split(rng, k)
        a = L.rand_transv_in(rng, E, int(rng.integers(2, 7)))
        b = L.rand_transv_in(rng, F, int(rng.integers(2, 7)))
        oa, ob = L.order_of(a), L.order_of(b)
        pairs = [(da, db) for da in L.divisors(oa) for db in L.divisors(ob)
                 if da > 1 and db > 1 and dmin <= da * db <= dmax]
        if not pairs:
            continue
        for i in rng.permutation(len(pairs))[:perk]:
            da, db = pairs[i]
            yield dict(mode='pair', order=da * db, gens=[L.mpow(a, oa // da), L.mpow(b, ob // db)],
                       parent_order=(oa, ob), nref=k,
                       desc=f'k={k}: a of order {da} in U (dim {k}) times b of order {db} in U-perp (dim {7 - k}), '
                            f'|a|={oa}, |b|={ob}')


def load_seen():
    seen, best = set(), 0
    if os.path.exists(RUNLOG):
        with open(RUNLOG) as f:
            for line in f:
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                seen.add(r.get('fp'))
                best = max(best, r.get('weight', 0) or 0)
    return seen, best


def save_gens(fp, grp):
    path = os.path.join(GENS, f'{fp}.txt')
    with open(path, 'w') as f:
        f.write(f'# {grp["desc"]}\n')
        for i, g in enumerate(grp['gens']):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(g))
    return os.path.relpath(path, HERE)


def analyse_group(gens):
    perms = [L.perm_of(g) for g in gens]
    lab = L.orbit_labels(perms)
    sizes, rep, good = L.analyse(lab)
    fp = hashlib.sha1(L.fingerprint(sizes, good).encode()).hexdigest()[:16]
    return lab, sizes, rep, good, fp


def evaluate(grp, args, seed, analysis):
    t_eval = time.process_time()
    lab, sizes, rep, good, fp = analysis
    rec = dict(q=8, mode=grp['mode'], order=grp['order'], desc=grp['desc'], fp=fp, seed=seed,
               norbits=int(sizes.size), K=int(good.size), weight=0, optimal=None, skipped=None)
    rec['gens_file'] = save_gens(fp, grp)
    K = int(good.size)
    if K == 0:
        rec['skipped'] = 'no good orbits'
        return rec, None
    if K > args.kmax:
        rec['skipped'] = f'K={K} > kmax'
        return rec, None
    rows = L.compat_packed(lab, rep, good)
    rec['density'] = round(L.packed_density(rows), 5)
    w = sizes[good]
    os.makedirs(WORK, exist_ok=True)
    gbin = os.path.join(WORK, f'{fp}.bin')
    gclq = os.path.join(WORK, f'{fp}.clq')
    L.write_graph_packed(gbin, rows, w)
    cmd = [WCLQ, gbin, str(args.texact), str(args.theur), str(seed), gclq]
    subprocess.run(cmd, capture_output=True, text=True, timeout=args.texact + args.theur + 120)
    weight, opt, verts = L.read_clique(gclq)
    rec['weight'] = int(weight)
    rec['optimal'] = bool(opt)
    os.remove(gbin)
    os.remove(gclq)
    chosen = good[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    idx = np.flatnonzero(np.isin(lab, chosen))
    if idx.size != weight or not L.pairwise_ok(idx):
        rec['skipped'] = 'verification failed'
        return rec, None
    rec['cpu_eval'] = round(time.process_time() - t_eval, 2)
    return rec, idx


def write_best(idx, grp, weight):
    with open(BEST_IDX, 'w') as f:
        f.write(f'# {weight} points, pairwise opposite (orbit union, verified); generators in best_raw_gen.txt\n')
        f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    with open(BEST_GEN, 'w') as f:
        f.write(f'# {weight} points: {grp["desc"]}\n')
        for i, g in enumerate(grp['gens']):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(g))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['cyc', 'pair'], required=True)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cpu', type=float, default=480.0)
    ap.add_argument('--texact', type=float, default=3.0)
    ap.add_argument('--theur', type=float, default=0.5)
    ap.add_argument('--dmin', type=int, default=5)
    ap.add_argument('--dmax', type=int, default=600)
    ap.add_argument('--pairk', default='2,4')
    ap.add_argument('--perk', type=int, default=4)
    ap.add_argument('--kmax', type=int, default=8000)
    ap.add_argument('--maxgroups', type=int, default=10 ** 9)
    args = ap.parse_args()
    os.makedirs(GENS, exist_ok=True)
    os.makedirs(WORK, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    ks = [int(x) for x in args.pairk.split(',') if x]
    seen, best_known = load_seen()
    start = cpu_total()
    reserve = args.texact + args.theur + 20
    gen = (cyc_samples(rng, args.dmin, args.dmax) if args.mode == 'cyc'
           else pair_samples(rng, args.dmin, args.dmax, ks, args.perk))
    n_eval = n_skip = tried = 0
    best_here = 0
    while cpu_total() - start < args.cpu - reserve and tried < args.maxgroups:
        grp = next(gen)
        tried += 1
        analysis = analyse_group(grp['gens'])
        fp = analysis[-1]
        if fp in seen:
            n_skip += 1
            continue
        seen.add(fp)
        rec, idx = evaluate(grp, args, args.seed * 1000 + tried, analysis)
        rec['t_cpu_total'] = round(cpu_total() - start, 1)
        with open(RUNLOG, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        if idx is not None and not os.path.exists(os.path.join(GENS, f'{fp}.txt')):
            pass
        gp = os.path.join(GENS, f'{fp}.txt')
        n_eval += 1
        print(f"[{rec['t_cpu_total']:7.1f}s] {grp['mode']} d={grp['order']} K={rec['K']} norb={rec['norbits']} "
              f"w={rec['weight']} opt={rec['optimal']} skip={rec['skipped']}", flush=True)
        if idx is not None and rec['weight'] > max(best_known, best_here):
            best_here = rec['weight']
            write_best(idx, grp, rec['weight'])
            print('NEW BEST', rec['weight'], grp['desc'], flush=True)
    print(f'done: evaluated {n_eval}, skipped as repeats {n_skip}, sampled {tried}, best this run {best_here}, '
          f'cpu {cpu_total() - start:.1f}s', flush=True)


if __name__ == '__main__':
    main()
