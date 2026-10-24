#!/usr/bin/env python3
"""Card c3 (squad round 3): deeper orbit unions.  Driver.

mode cyc : cyclic subgroups <h> of O(7,11), h = g^(|g|/d) for a random isometry g (product of reflections) and
           d in the target orders (default 44 55 66 88 110 132 220).
mode pair: two-generator abelian groups G = <a> x <b>, where a is an isometry of a random non-degenerate subspace U
           (dimension k in 2..5) and b an isometry of U-perp, so a and b commute (they act on complementary subspaces).
           a and b are powers of random products of reflections, so G = <a'> x <b'> with prescribed orders.
For every group: orbits of G on the 177,156 points, good orbits, the orbit compatibility graph, and a maximum-weight
clique (weight = orbit size) from wclq (exact branch and bound, local search if cut).  Every group is written to
gens/<fingerprint>.txt (its generator matrices, reproducible); groups whose orbit-structure fingerprint was already seen
are skipped.  The best union is written to best_idx.txt (point indices) with its generators in best_gen.txt.

usage: run_groups.py --mode cyc|pair --seed S --cpu CPU [--texact T] [--theur T2] [--targets 44,55] [--kmax 6000]
CPU is the total CPU budget (driver + wclq children) in seconds; keep it <= 600.
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
import orbl as L  # noqa: E402

WCLQ = os.path.join(HERE, 'wclq')
WORK = os.path.join(HERE, 'work')
GENS = os.path.join(HERE, 'gens')
RUNLOG = os.path.join(HERE, 'runlog.jsonl')
BEST_IDX = os.path.join(HERE, 'best_idx.txt')
BEST_GEN = os.path.join(HERE, 'best_gen.txt')


def cpu_total():
    t = os.times()
    return t.user + t.system + t.children_user + t.children_system


def divisors_from_factor(m):
    """all divisors of m, where m divides |O(7,11)| (so its prime factors lie in L.PRIMES)."""
    divs = [1]
    for pr in L.PRIMES:
        if m % pr:
            continue
        e = 0
        while m % pr == 0:
            m //= pr
            e += 1
        divs = [d * pr ** k for d in divs for k in range(e + 1)]
    assert m == 1, 'order has a prime factor outside PRIMES'
    return sorted(divs)


def cyc_samples(rng, targets):
    while True:
        k = int(rng.integers(3, 13))
        g = L.rand_isom(rng, k)
        m = L.order_of(g)
        for d in targets:
            if m % d == 0:
                h = L.mpow(g, m // d)
                yield dict(mode='cyc', order=d, gens=[h], parent_order=m, parent=g, nref=k,
                           desc=f'cyclic order {d}: h = g^({m // d}), g = product of {k} reflections, |g| = {m}')


def z11_samples(rng):
    """unipotent subgroups <u> of order 11: u = g^(|g|/11) for random isometries g with 11 | |g|."""
    while True:
        k = int(rng.integers(3, 13))
        g = L.rand_isom(rng, k)
        m = L.order_of(g)
        if m % 11:
            continue
        u = L.mpow(g, m // 11)
        yield dict(mode='z11', order=11, gens=[u], parent_order=m, parent=g, nref=k,
                   desc=f'unipotent order 11: u = g^({m // 11}), g = product of {k} reflections, |g| = {m}')


def pair_samples(rng, per_sample=6, kfix=None):
    while True:
        k = int(rng.integers(2, 6)) if kfix is None else kfix
        E, F = L.split(rng, k)
        a = L.rand_refl_in(rng, E, int(rng.integers(2, 9)))
        b = L.rand_refl_in(rng, F, int(rng.integers(2, 9)))
        oa, ob = L.order_of(a), L.order_of(b)
        pairs = [(da, db) for da in divisors_from_factor(oa) for db in divisors_from_factor(ob)
                 if da > 1 and db > 1 and 22 <= da * db <= 660]
        if not pairs:
            continue
        order = rng.permutation(len(pairs))
        for i in order[:per_sample]:
            da, db = pairs[i]
            a2 = L.mpow(a, oa // da)
            b2 = L.mpow(b, ob // db)
            yield dict(mode='pair', order=da * db, gens=[a2, b2], parent_order=(oa, ob), parent=(a, b), nref=k,
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


def analyse_group(grp):
    perms = [L.perm_of(g) for g in grp['gens']]
    lab = L.orbit_labels(perms)
    sizes, rep, good = L.analyse(lab)
    fp = hashlib.sha1(L.fingerprint(sizes, good).encode()).hexdigest()[:16]
    return lab, sizes, rep, good, fp


def evaluate(grp, args, seed, analysis):
    t_eval = time.process_time()
    lab, sizes, rep, good, fp = analysis
    rec = dict(mode=grp['mode'], order=grp['order'], desc=grp['desc'], fp=fp, seed=seed,
               norbits=int(sizes.size), K=int(good.size), weight=0, optimal=None, skipped=None)
    gpath = save_gens(fp, grp)
    rec['gens_file'] = gpath
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
    cmd = [os.path.join(HERE, args.solver), gbin, str(args.texact), str(args.theur), str(seed), gclq]
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
        f.write(f'# {weight} points, pairwise opposite (verified by wclq + numpy); generator in best_gen.txt\n')
        f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    with open(BEST_GEN, 'w') as f:
        f.write(f'# {weight} points: {grp["desc"]}\n')
        for i, g in enumerate(grp['gens']):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(g))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--mode', choices=['cyc', 'pair', 'z11'], required=True)
    ap.add_argument('--solver', default='wclq2')
    ap.add_argument('--pairk', type=int, default=None)
    ap.add_argument('--perk', type=int, default=6)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cpu', type=float, default=500.0)
    ap.add_argument('--texact', type=float, default=30.0)
    ap.add_argument('--theur', type=float, default=5.0)
    ap.add_argument('--targets', default='44,55,66,88,110,132,220')
    ap.add_argument('--kmax', type=int, default=6000)
    ap.add_argument('--maxgroups', type=int, default=10 ** 9)
    args = ap.parse_args()
    os.makedirs(GENS, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    targets = [int(x) for x in args.targets.split(',') if x]
    seen, best_known = load_seen()
    start = cpu_total()
    reserve = args.texact + args.theur + 15
    gen = {'cyc': lambda: cyc_samples(rng, targets), 'pair': lambda: pair_samples(rng, args.perk, args.pairk),
           'z11': lambda: z11_samples(rng)}[args.mode]()
    n_eval = n_skip = 0
    best_here = 0
    tried = 0
    while cpu_total() - start < args.cpu - reserve and tried < args.maxgroups:
        grp = next(gen)
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
            with open(os.path.join(HERE, 'best_weight.txt'), 'w') as f:
                f.write(f'{rec["weight"]}\n')
            print('NEW BEST', rec['weight'], rec['desc'], flush=True)
    print(f'done: evaluated {n_eval}, skipped as repeats {n_skip}, sampled {tried}, '
          f'best this run {best_here}, cpu {cpu_total() - start:.1f}s', flush=True)


if __name__ == '__main__':
    main()
