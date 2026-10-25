#!/usr/bin/env python3
"""Card c3 (squad round 6): orbit unions for NEW block shapes of commuting isometries of Q(6,11).

A group is G = <g_1> x ... x <g_r> where g_i acts on a non-degenerate block E_i of an orthogonal decomposition
V = E_1 + ... + E_r (identity on the other blocks), so the g_i commute.  The shape is a list of (dim:target) pairs:
block i has dimension dim_i and g_i has order exactly target_i (a power of a random element of O(E_i) whose order is
divisible by target_i; decompositions whose blocks admit no such element are redrawn).  Shapes are given as
"4:5,3:3" (4+3, orders 5 and 3, so G = Z15) and several shapes as "a;b;c".

For each group: orbits on the 177,156 points of Q(6,11), good orbits (internally pairwise opposite), the orbit
compatibility graph, and a maximum-weight clique (weight = orbit size) by wclq2 (exact branch and bound with a CPU cap,
then tabu local search).  Groups with an already-seen orbit-structure fingerprint are skipped.  The best union is
written to best_idx.txt (point indices, verified by wclq2's graph and by numpy) with its generators in best_gen.txt.

usage: shapes6.py --shapes "4:5,3:3;4:3,3:5" [--draws N] [--seed S] [--cpu C] [--texact T] [--theur H] [--kmax K]
CPU: the driver and its wclq2 children; no new group starts once the CPU total would exceed --cpu.
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
import compat6 as C6  # noqa: E402  (C kernel: same rows as L.compat_packed, ~30x faster)

p = L.p
J = L.J
mpow = L.mpow
WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
GENS = os.path.join(HERE, 'gens')
RUNLOG = os.path.join(HERE, 'runlog.jsonl')
BEST_IDX = os.path.join(HERE, 'best_idx.txt')
BEST_GEN = os.path.join(HERE, 'best_gen.txt')


def cpu_total():
    t = os.times()
    return t.user + t.system + t.children_user + t.children_system


def nondeg_in(rng, F, k):
    """k vectors spanning a non-degenerate k-dim subspace of the span of the rows of F."""
    E = []
    while len(E) < k:
        c = rng.integers(0, p, F.shape[0])
        v = (c @ F) % p
        for e in E:
            ee = int(e @ J @ e) % p
            v = (v - (int(v @ J @ e) % p) * pow(ee, p - 2, p) * e) % p
        if int(v @ J @ v) % p:
            E.append(v)
    return np.array(E, dtype=np.int64)


def orth_blocks(rng, dims):
    """V = E_1 + ... + E_r, B-orthogonal non-degenerate blocks of the given dimensions (rows = bases)."""
    blocks = []
    F = np.eye(7, dtype=np.int64)
    for d in dims[:-1]:
        E = nondeg_in(rng, F, d)
        blocks.append(E)
        M = (F @ J @ E.T) % p
        N = L.nullspace_mod(M.T % p)
        F = (N @ F) % p
    blocks.append(F)
    assert sum(b.shape[0] for b in blocks) == 7
    return blocks


def sample_group(rng, dims, targets, tries_block=400, tries_dec=40):
    """random decomposition with the given block dims and generators of exact orders targets (1 = block unused)."""
    for _ in range(tries_dec):
        blocks = orth_blocks(rng, dims)
        gens, ords, ok = [], [], True
        for E, d in zip(blocks, targets):
            if d == 1:
                continue
            found = None
            for _ in range(tries_block):
                g = L.rand_refl_in(rng, E, int(rng.integers(2, 9)))
                o = L.order_of(g)
                if o > 1 and o % d == 0:
                    found = mpow(g, o // d)
                    break
            if found is None:
                ok = False
                break
            gens.append(found)
            ords.append(d)
        if ok:
            return gens, ords
    return None


def parse_shapes(text):
    out = []
    for part in text.split(';'):
        part = part.strip()
        if not part:
            continue
        dims, targets = [], []
        for item in part.split(','):
            d, t = item.split(':')
            dims.append(int(d))
            targets.append(int(t))
        assert sum(dims) == 7, part
        assert sum(1 for t in targets if t > 1) >= 2, 'need at least two non-trivial blocks: ' + part
        out.append((part, dims, targets))
    return out


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


def save_gens(fp, desc, gens):
    path = os.path.join(GENS, f'{fp}.txt')
    with open(path, 'w') as f:
        f.write(f'# {desc}\n')
        for i, g in enumerate(gens):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(g))
    return os.path.relpath(path, HERE)


def write_best(idx, desc, gens, weight):
    with open(BEST_IDX, 'w') as f:
        f.write(f'# {weight} points, pairwise opposite (verified by wclq2 + numpy); generators in best_gen.txt\n')
        f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    with open(BEST_GEN, 'w') as f:
        f.write(f'# {weight} points: {desc}\n')
        for i, g in enumerate(gens):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(g))


def analyse(gens):
    perms = [L.perm_of(g) for g in gens]
    lab = L.orbit_labels(perms)
    sizes, rep, good = L.analyse(lab)
    fp = hashlib.sha1(L.fingerprint(sizes, good).encode()).hexdigest()[:16]
    return lab, sizes, rep, good, fp


def evaluate(shape, gens, ords, analysis, args, seed, tag):
    t_eval = time.process_time()
    lab, sizes, rep, good, fp = analysis
    K = int(good.size)
    desc = f'shape {shape}: group order {int(np.prod(ords))}, generator orders {ords}'
    rec = dict(card='c3', round=6, shape=shape, desc=desc, tag=tag, fp=fp, seed=seed, norbits=int(sizes.size),
               K=K, weight=0, optimal=None, skipped=None, orbit_sizes=sorted(set(sizes.tolist()))[:40])
    rec['gens_file'] = save_gens(fp, desc, gens)
    if K == 0:
        rec['skipped'] = 'no good orbits'
        return rec, None
    if K > args.kmax:
        rec['skipped'] = f'K={K} > kmax'
        return rec, None
    rows = C6.compat_rows(lab, rep, good)
    w = sizes[good]
    os.makedirs(WORK, exist_ok=True)
    gbin = os.path.join(WORK, f'{fp}.bin')
    gclq = os.path.join(WORK, f'{fp}.clq')
    L.write_graph_packed(gbin, rows, w)
    if K <= args.ksmall:
        texact, theur = args.texact_small, args.theur_small
    else:
        texact, theur = args.texact, args.theur
    cmd = [WCLQ, gbin, str(texact), str(theur), str(seed), gclq]
    t_cl = time.process_time()
    res = subprocess.run(cmd, capture_output=True, text=True, timeout=texact + theur + 300)
    rec['cpu_clique_driver_side'] = round(time.process_time() - t_cl, 2)
    weight, opt, verts = L.read_clique(gclq)
    rec['weight'] = int(weight)
    rec['optimal'] = bool(opt)
    rec['texact'] = texact
    rec['theur'] = theur
    rec['density'] = round(L.packed_density(rows), 5)
    rec['solver_stderr'] = [x for x in res.stderr.strip().splitlines()[-2:]]
    for fpath in (gbin, gclq):
        if os.path.exists(fpath):
            os.remove(fpath)
    chosen = good[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    idx = np.flatnonzero(np.isin(lab, chosen))
    if idx.size != weight or not L.pairwise_ok(idx):
        rec['skipped'] = 'verification failed'
        return rec, None
    rec['cpu_eval'] = round(time.process_time() - t_eval, 2)
    return rec, idx


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--shapes', required=True)
    ap.add_argument('--draws', type=int, default=3, help='random group samples per shape')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cpu', type=float, default=540.0)
    ap.add_argument('--texact', type=float, default=15.0)
    ap.add_argument('--theur', type=float, default=60.0)
    ap.add_argument('--texact_small', type=float, default=30.0)
    ap.add_argument('--theur_small', type=float, default=5.0)
    ap.add_argument('--ksmall', type=int, default=1500)
    ap.add_argument('--kmax', type=int, default=14000)
    args = ap.parse_args()
    for d in (GENS, WORK):
        os.makedirs(d, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    shapes = parse_shapes(args.shapes)
    seen, best_known = load_seen()
    start = cpu_total()
    reserve = args.texact + args.theur + 40
    best_here = 0
    n_eval = n_rep = n_nosample = 0
    counter = 0
    for draw in range(args.draws):
        if cpu_total() - start > args.cpu - reserve:
            break
        for shape, dims, targets in shapes:
            if cpu_total() - start > args.cpu - reserve:
                break
            s = sample_group(rng, dims, targets)
            if s is None:
                n_nosample += 1
                rec = dict(card='c3', round=6, shape=shape, skipped='no decomposition with the required orders',
                           t_cpu_total=round(cpu_total() - start, 1))
                with open(RUNLOG, 'a') as f:
                    f.write(json.dumps(rec) + '\n')
                print(f'[{rec["t_cpu_total"]:7.1f}s] {shape}: no element of the required orders found', flush=True)
                continue
            gens, ords = s
            analysis = analyse(gens)
            fp = analysis[-1]
            if fp in seen:
                n_rep += 1
                print(f'[{cpu_total() - start:7.1f}s] {shape}: repeat of an orbit structure already run', flush=True)
                continue
            seen.add(fp)
            counter += 1
            seed = args.seed * 1000 + counter
            rec, idx = evaluate(shape, gens, ords, analysis, args, seed, f'draw{draw}')
            rec['t_cpu_total'] = round(cpu_total() - start, 1)
            with open(RUNLOG, 'a') as f:
                f.write(json.dumps(rec) + '\n')
            n_eval += 1
            print(f"[{rec['t_cpu_total']:7.1f}s] {shape} K={rec['K']} norb={rec['norbits']} w={rec['weight']} "
                  f"opt={rec['optimal']} skip={rec['skipped']}", flush=True)
            if idx is not None and rec['weight'] > max(best_known, best_here):
                best_here = rec['weight']
                write_best(idx, rec['desc'], gens, rec['weight'])
                with open(os.path.join(HERE, 'best_weight.txt'), 'w') as f:
                    f.write(f'{rec["weight"]}\n')
                print('NEW BEST', rec['weight'], rec['desc'], flush=True)
    print(f'done: evaluated {n_eval}, repeats {n_rep}, no-sample {n_nosample}, best this run {best_here}, '
          f'cpu {cpu_total() - start:.1f}s', flush=True)


if __name__ == '__main__':
    main()
