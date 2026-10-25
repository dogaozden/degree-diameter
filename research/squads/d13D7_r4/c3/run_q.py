#!/usr/bin/env python3
"""run_q.py (card c3, squad round 4): orbit-union search for pairwise-opposite point sets of H(q), q = 5 or 7.

Port of research/squads/d13D7_r3/c3/run_groups.py.  Modes:
  cyc   : cyclic subgroups <h>, h = g^(m/d), for random isometries g (products of k reflections, m = |g|), for every
          divisor d of m with dmin <= d <= dmax.
  pair  : commuting pairs G = <a'> x <b'>: a on a random non-degenerate U (dim k in --pairk), b on U-perp, a' = a^(|a|/da),
          b' = b^(|b|/db), over all (da, db) with da, db > 1 and dmin <= da*db <= dmax.
  gens  : the group of a gens file (replay), for a longer exact search.
For every group: orbits, good orbits (internally pairwise opposite), compatibility, exact maximum-weight clique (wclq2:
branch and bound for TEXACT CPU seconds, then tabu local search for THEUR), numpy re-verification of the union.
Groups are deduplicated by the orbit-structure fingerprint (within a run and across the runlog of this q).
Outputs (in this folder): runlog_q<q>.jsonl, gens/<fp>.txt, work/, and when a union beats the stored best:
  best_q<q>_idx.txt (point indices), best_q<q>_gen.txt (generators), best_q<q>_weight.txt.
usage: run_q.py --q 7 --mode cyc|pair|gens [--seed S] [--cpu SEC] [--dmin 6] [--dmax 400] [--pairk 3,4,5]
                [--kmax 4000] [--texact 3] [--theur 0.5] [--gensfile F]
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
import orbq as L  # noqa: E402

WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
GENS = os.path.join(HERE, 'gens')


def cpu_total():
    t = os.times()
    return t.user + t.system + t.children_user + t.children_system


def cyc_samples(rng, dmin, dmax):
    while True:
        k = int(rng.integers(3, 13))
        g = L.rand_isom(rng, k)
        m = L.order_of(g)
        ds = [d for d in L.divisors(m) if dmin <= d <= dmax]
        for i in rng.permutation(len(ds)):
            d = ds[i]
            h = L.mpow(g, m // d)
            yield dict(mode='cyc', order=d, gens=[h], parent_order=m, nref=k,
                       desc=f'cyclic order {d}: h = g^({m // d}), g = product of {k} reflections, |g| = {m}')


def pair_samples(rng, dmin, dmax, ks):
    while True:
        k = int(ks[rng.integers(0, len(ks))])
        E, F = L.split(rng, k)
        a = L.rand_refl_in(rng, E, int(rng.integers(2, 9)))
        b = L.rand_refl_in(rng, F, int(rng.integers(2, 9)))
        oa, ob = L.order_of(a), L.order_of(b)
        pairs = [(da, db) for da in L.divisors(oa) for db in L.divisors(ob)
                 if da > 1 and db > 1 and dmin <= da * db <= dmax]
        for i in rng.permutation(len(pairs)):
            da, db = pairs[i]
            a2 = L.mpow(a, oa // da)
            b2 = L.mpow(b, ob // db)
            yield dict(mode='pair', order=da * db, gens=[a2, b2], parent_order=(oa, ob), nref=k,
                       desc=f'k={k}: a of order {da} in U (dim {k}) times b of order {db} in U-perp (dim {7 - k}), '
                            f'|a|={oa}, |b|={ob}')


def load_seen(runlog):
    seen, best = set(), 0
    if os.path.exists(runlog):
        with open(runlog) as f:
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


def evaluate(grp, args, seed, analysis, tag):
    """returns (record, point-index array or None)."""
    t_eval = time.process_time()
    lab, sizes, rep, good, fp = analysis
    rec = dict(q=L.p, mode=grp['mode'], order=grp['order'], desc=grp['desc'], fp=fp, seed=seed,
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
    w = sizes[good]
    os.makedirs(WORK, exist_ok=True)
    gbin = os.path.join(WORK, f'{tag}.bin')
    gclq = os.path.join(WORK, f'{tag}.clq')
    L.write_graph_packed(gbin, rows, w)
    t_cl = time.process_time()
    cmd = [WCLQ, gbin, str(args.texact), str(args.theur), str(seed), gclq]
    if args.init:
        init_pts = np.loadtxt(args.init, comments='#', dtype=np.int64).reshape(-1)
        labs = np.unique(lab[init_pts])
        pos = np.full(sizes.size, -1, np.int64)
        pos[good] = np.arange(K)
        gi = pos[labs]
        if np.any(gi < 0):
            rec['init'] = 'init set uses a non-good orbit; ignored'
        else:
            union = np.flatnonzero(np.isin(lab, labs))
            rec['init'] = 'union' if np.array_equal(np.sort(union), np.sort(init_pts)) else 'not a union'
            if rec['init'] == 'union':
                ipath = os.path.join(WORK, f'{tag}_init.txt')
                with open(ipath, 'w') as f:
                    f.write('\n'.join(map(str, gi.tolist())) + '\n')
                cmd.append(ipath)
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


def write_best(idx, desc, gens, weight):
    with open(os.path.join(HERE, f'best_q{L.p}_idx.txt'), 'w') as f:
        f.write(f'# {weight} points, pairwise opposite in H({L.p}) (verified by wclq2 + numpy); generators in '
                f'best_q{L.p}_gen.txt\n')
        f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    with open(os.path.join(HERE, f'best_q{L.p}_gen.txt'), 'w') as f:
        f.write(f'# {weight} points: {desc}\n')
        for i, g in enumerate(gens):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(g))
    with open(os.path.join(HERE, f'best_q{L.p}_weight.txt'), 'w') as f:
        f.write(f'{weight}\n')


def stored_best():
    path = os.path.join(HERE, f'best_q{L.p}_weight.txt')
    if os.path.exists(path):
        return int(open(path).read().strip())
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--q', type=int, required=True)
    ap.add_argument('--mode', choices=['cyc', 'pair', 'gens'], required=True)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cpu', type=float, default=500.0)
    ap.add_argument('--dmin', type=int, default=6)
    ap.add_argument('--dmax', type=int, default=400)
    ap.add_argument('--pairk', default='3,4,5')
    ap.add_argument('--kmax', type=int, default=4000)
    ap.add_argument('--texact', type=float, default=3.0)
    ap.add_argument('--theur', type=float, default=0.5)
    ap.add_argument('--maxgroups', type=int, default=10 ** 9)
    ap.add_argument('--gensfile', default=None)
    ap.add_argument('--init', default=None, help='point-index file: warm-start clique (must be a union of orbits)')
    args = ap.parse_args()
    L.setq(args.q)
    os.makedirs(GENS, exist_ok=True)
    runlog = os.path.join(HERE, f'runlog_q{args.q}.jsonl')
    rng = np.random.default_rng(args.seed)
    seen, _ = load_seen(runlog)
    best_known = stored_best()
    start = cpu_total()
    reserve = args.texact + args.theur + 15
    if args.mode == 'gens':
        desc, gens = L.read_gens(args.gensfile)
        samples = iter([dict(mode='gens', order=-1, gens=gens, parent_order=None, nref=None, desc=desc)])
    else:
        ks = [int(x) for x in args.pairk.split(',') if x]
        samples = {'cyc': lambda: cyc_samples(rng, args.dmin, args.dmax),
                   'pair': lambda: pair_samples(rng, args.dmin, args.dmax, ks)}[args.mode]()
    n_eval = n_skip = tried = best_here = 0
    while cpu_total() - start < args.cpu - reserve and tried < args.maxgroups:
        try:
            grp = next(samples)
        except StopIteration:
            break
        tried += 1
        analysis = analyse_group(grp['gens'])
        fp = analysis[-1]
        if fp in seen and args.mode != 'gens':
            n_skip += 1
            continue
        seen.add(fp)
        tag = f'q{args.q}_s{args.seed}_{tried}'
        rec, idx = evaluate(grp, args, args.seed * 1000 + tried, analysis, tag)
        rec['t_cpu_total'] = round(cpu_total() - start, 1)
        with open(runlog, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        n_eval += 1
        print(f"[{rec['t_cpu_total']:7.1f}s] {grp['mode']} d={grp['order']} K={rec['K']} norb={rec['norbits']} "
              f"w={rec['weight']} opt={rec['optimal']} skip={rec['skipped']}", flush=True)
        if idx is not None and args.mode == 'gens':
            with open(os.path.join(HERE, f'set_q{args.q}_{tag}_w{rec["weight"]}.txt'), 'w') as f:
                f.write(f'# {rec["weight"]} points, pairwise opposite (gens mode: {grp["desc"][:80]})\n')
                f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
        if idx is not None and rec['weight'] > max(best_known, best_here):
            best_here = rec['weight']
            write_best(idx, grp['desc'], grp['gens'], rec['weight'])
            print('NEW BEST', rec['weight'], grp['desc'], flush=True)
    print(f'done: evaluated {n_eval}, skipped as repeats {n_skip}, sampled {tried}, best this run {best_here}, '
          f'cpu {cpu_total() - start:.1f}s', flush=True)


if __name__ == '__main__':
    main()
