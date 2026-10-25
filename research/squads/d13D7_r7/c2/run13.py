#!/usr/bin/env python3
"""Card c2 (squad round 4, job cell-13-7): orbit-union driver for H(13).  Port of r3/c3/run_groups.py.

mode cyc : cyclic subgroups <h> of O(7,13): h = g^(|g|/d), g a random product of reflections, d in the target orders.
mode pair: G = <a> x <b>, a an isometry of a random non-degenerate k-dim U (default k = 5), b an isometry of U-perp
           (dim 7-k); a and b commute.  a, b are powers of random products of reflections in U and U-perp, and the
           pair (order of a, order of b) is any pair of divisors with product in [lo, hi].
For every group: orbits, good orbits, the compatibility graph, and a maximum-weight clique (weight = orbit size) by
wclq2 (exact branch and bound, tabu local search if cut).  Every group is written to gens/<fp>.txt (reproducible);
groups with an already-seen orbit-structure fingerprint are skipped.  The best union so far is written to best_idx.txt
(point indices, verified) with its generators in best_gen.txt.

usage: run13.py --mode cyc|pair --seed S --cpu CPU [--texact T] [--theur T2] [--targets ...] [--pairk 5] [--lo 14] [--hi 700]
CPU is the total CPU budget (driver + wclq2 children) in seconds.
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
import orbq13 as L  # noqa: E402

WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
GENS = os.path.join(HERE, 'gens')
RUNLOG = os.path.join(HERE, 'runlog13.jsonl')
R4_RUNLOG = '/home/user/degree-diameter/research/squads/d13D7_r4/c2/runlog13.jsonl'
BEST_IDX = os.path.join(HERE, 'best_idx.txt')
BEST_GEN = os.path.join(HERE, 'best_gen.txt')
BEST_W = os.path.join(HERE, 'best_weight.txt')


def cpu_total():
    t = os.times()
    return t.user + t.system + t.children_user + t.children_system


def cyc_samples(rng, targets, dlo=14, dhi=400, perg=3, kmin=3, kmax_refl=12):
    """targets None: for each random g take up to perg divisors d of |g| with dlo <= d <= dhi (random order)."""
    while True:
        k = int(rng.integers(kmin, kmax_refl + 1))
        g = L.rand_isom(rng, k)
        m = L.order_of(g)
        if targets is None:
            ds = [d for d in L.divisors_from_factor(m) if dlo <= d <= dhi]
            if not ds:
                continue
            ds = [ds[i] for i in rng.permutation(len(ds))[:perg]]
        else:
            ds = [d for d in targets if m % d == 0]
        for d in ds:
            if m % d == 0:
                h = L.mpow(g, m // d)
                yield dict(mode='cyc', order=d, gens=[h], parent_order=m, nref=k,
                           desc=f'cyclic order {d}: h = g^({m // d}), g = product of {k} reflections, |g| = {m}')


def pair_samples(rng, per_sample, kfix, lo, hi):
    while True:
        k = kfix
        E, F = L.split(rng, k)
        a = L.rand_refl_in(rng, E, int(rng.integers(2, 9)))
        b = L.rand_refl_in(rng, F, int(rng.integers(2, 9)))
        oa, ob = L.order_of(a), L.order_of(b)
        pairs = [(da, db) for da in L.divisors_from_factor(oa) for db in L.divisors_from_factor(ob)
                 if da > 1 and db > 1 and lo <= da * db <= hi]
        if not pairs:
            continue
        order = rng.permutation(len(pairs))
        for i in order[:per_sample]:
            da, db = pairs[i]
            a2 = L.mpow(a, oa // da)
            b2 = L.mpow(b, ob // db)
            yield dict(mode='pair', order=da * db, gens=[a2, b2], parent_order=(oa, ob), nref=k,
                       desc=f'k={k}: a of order {da} in U (dim {k}) times b of order {db} in U-perp (dim {7 - k}), '
                            f'|a|={oa}, |b|={ob}')


def pair_target_samples(rng, kfix, targets, lo, hi, tries_max=1000):
    """round robin over target (order of a, order of b) pairs; every yield uses a fresh random U, a, b."""
    dead = set()
    i = 0
    while len(dead) < len(targets):
        da, db = targets[i % len(targets)]
        i += 1
        if (da, db) in dead:
            continue
        ok = False
        for _ in range(tries_max):
            E, F = L.split(rng, kfix)
            a = L.rand_refl_in(rng, E, int(rng.integers(2, 9)))
            b = L.rand_refl_in(rng, F, int(rng.integers(2, 9)))
            oa, ob = L.order_of(a), L.order_of(b)
            if oa % da == 0 and ob % db == 0 and lo <= da * db <= hi:
                ok = True
                break
        if not ok:
            dead.add((da, db))
            print(f'no sample for a={da} b={db} in {tries_max} tries', flush=True)
            continue
        yield dict(mode='pair', order=da * db, gens=[L.mpow(a, oa // da), L.mpow(b, ob // db)], parent_order=(oa, ob),
                   nref=kfix, desc=f'k={kfix}: a of order {da} in U (dim {kfix}) times b of order {db} in U-perp '
                                    f'(dim {7 - kfix}), |a|={oa}, |b|={ob}')


def load_seen():
    seen, best = set(), 0
    if os.path.exists(R4_RUNLOG):
        with open(R4_RUNLOG) as f:
            for line in f:
                try:
                    seen.add(json.loads(line).get('fp'))
                except ValueError:
                    pass
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


def analyse_group(grp):
    perms = [L.perm_of(g) for g in grp['gens']]
    lab = L.orbit_labels(perms)
    sizes, rep, good = L.analyse(lab)
    fp = hashlib.sha1(L.fingerprint(sizes, good).encode()).hexdigest()[:16]
    return lab, sizes, rep, good, fp


def evaluate(grp, args, seed, analysis):
    t_eval = time.process_time()
    lab, sizes, rep, good, fp = analysis
    rec = dict(q=13, mode=grp['mode'], order=grp['order'], desc=grp['desc'], fp=fp, seed=seed,
               norbits=int(sizes.size), K=int(good.size), weight=0, optimal=None, skipped=None)
    rec['gens_file'] = save_gens(fp, grp)
    K = good.size
    if K == 0:
        rec['skipped'] = 'no good orbits'
        return rec, None
    if K > args.kmax:
        rec['skipped'] = f'K={K} > kmax'
        return rec, None
    rows = L.compat_packed(lab, rep, good)
    w = sizes[good]
    os.makedirs(WORK, exist_ok=True)
    gbin = os.path.join(WORK, f'{fp}.bin')
    gclq = os.path.join(WORK, f'{fp}.clq')
    L.write_graph_packed(gbin, rows, w)
    t_cl = time.process_time()
    cmd = [WCLQ, gbin, str(args.texact), str(args.theur), str(seed), gclq]
    res = subprocess.run(cmd, capture_output=True, text=True, timeout=args.texact + args.theur + 120)
    rec['cpu_clique_driver_side'] = round(time.process_time() - t_cl, 2)
    weight, opt, verts = L.read_clique(gclq)
    rec['weight'] = int(weight)
    rec['optimal'] = bool(opt)
    rec['edges_density'] = round(L.packed_density(rows), 5)
    os.remove(gbin)
    os.remove(gclq)
    chosen = good[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    idx = np.flatnonzero(np.isin(lab, chosen))
    if idx.size != weight or not L.pairwise_ok(idx):
        rec['skipped'] = 'verification failed'
        return rec, None
    rec['cpu_eval'] = round(time.process_time() - t_eval, 2)
    rec['clique_stderr'] = res.stderr.strip().splitlines()[-1:] if res.stderr else []
    return rec, idx


def write_best(idx, grp, weight):
    with open(BEST_IDX, 'w') as f:
        f.write(f'# {weight} points, pairwise opposite in H(13) (verified by wclq2 + numpy); generators in best_gen.txt\n')
        f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    with open(BEST_GEN, 'w') as f:
        f.write(f'# {weight} points: {grp["desc"]}\n')
        for i, g in enumerate(grp['gens']):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(g))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['cyc', 'pair', 'pairt'], required=True)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cpu', type=float, default=500.0)
    ap.add_argument('--texact', type=float, default=15.0)
    ap.add_argument('--theur', type=float, default=5.0)
    ap.add_argument('--pairk', type=int, default=5)
    ap.add_argument('--perk', type=int, default=6)
    ap.add_argument('--lo', type=int, default=14)
    ap.add_argument('--hi', type=int, default=700)
    ap.add_argument('--targets', default='auto')
    ap.add_argument('--pairs', default='')
    ap.add_argument('--dlo', type=int, default=14)
    ap.add_argument('--dhi', type=int, default=400)
    ap.add_argument('--perg', type=int, default=3)
    ap.add_argument('--kmax', type=int, default=8000)
    ap.add_argument('--maxgroups', type=int, default=10 ** 9)
    args = ap.parse_args()
    os.makedirs(GENS, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    targets = None if args.targets == 'auto' else [int(x) for x in args.targets.split(',') if x]
    seen, best_known = load_seen()
    start = cpu_total()
    reserve = args.texact + args.theur + 20
    ptargets = [tuple(int(v) for v in t.split('x')) for t in args.pairs.split(',') if t.strip()]
    if args.mode == 'cyc':
        gen = cyc_samples(rng, None if args.targets == 'auto' else targets, args.dlo, args.dhi, args.perg)
    elif args.mode == 'pairt':
        gen = pair_target_samples(rng, args.pairk, ptargets, args.lo, args.hi)
    else:
        gen = pair_samples(rng, args.perk, args.pairk, args.lo, args.hi)
    n_eval = n_skip = 0
    best_here = 0
    tried = 0
    while cpu_total() - start < args.cpu - reserve and tried < args.maxgroups:
        try:
            grp = next(gen)
        except StopIteration:
            break
        tried += 1
        analysis = analyse_group(grp)
        fp = analysis[-1]
        if fp in seen:
            n_skip += 1
            continue
        seen.add(fp)
        rec, idx = evaluate(grp, args, args.seed * 1000 + tried, analysis)
        rec['t_cpu_total'] = round(cpu_total() - start, 1)
        with open(RUNLOG, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        n_eval += 1
        print(f"[{rec['t_cpu_total']:7.1f}s] {grp['mode']} d={grp['order']} K={rec['K']} "
              f"norb={rec['norbits']} w={rec['weight']} opt={rec['optimal']} skip={rec['skipped']}", flush=True)
        if idx is not None and rec['weight'] > max(best_known, best_here):
            best_here = rec['weight']
            write_best(idx, grp, rec['weight'])
            with open(BEST_W, 'w') as f:
                f.write(f'{rec["weight"]}\n')
            print('NEW BEST', rec['weight'], rec['desc'], flush=True)
    print(f'done: evaluated {n_eval}, skipped as repeats {n_skip}, sampled {tried}, '
          f'best this run {best_here}, cpu {cpu_total() - start:.1f}s', flush=True)


if __name__ == '__main__':
    main()
