#!/usr/bin/env python3
"""Card c1 (squad round 4): orbit unions of commuting block groups of O(7,11) acting on the points of H(11).

Builds on card c3 of round 3 (orbl.py, wclq2.c here are copies).  A group is G = <g_1> x ... x <g_r>, where g_i is an
isometry acting on a non-degenerate block E_i of an orthogonal decomposition V = E_1 + ... + E_r (identity on the other
blocks), so the g_i commute.  For each group: orbits on the points of Q(6,11), good orbits (internally pairwise
opposite), the compatibility graph, and a maximum-weight clique (wclq2: exact B&B, then tabu local search).

modes
  sub720  : every non-trivial subgroup of the 720 group G = <a> x <b> (a of order 15 on a 5-dim block, b of order 5 on
            the 2-dim perp), warm-started with the 720 set (a union of G-orbits, hence of every subgroup).
  blocks  : random orthogonal decomposition with block dimensions --dims (e.g. 5,2 / 4,3 / 6,1 / 3,2,2), random
            element of O(E_i) in each block, and the groups <g_i^(o_i/d_i)> of all prescribed order combinations
            d_i | o_i with prod d_i in [dmin, dmax] (at least two non-trivial blocks).

usage: sweep.py MODE [--dims 5,2] [--seed S] [--cpu C] [--texact T] [--theur H] [--kmax K] [--perdraw N]
                     [--dmin A] [--dmax B] [--maxgroups M]
CPU: the driver and its wclq2 children; the run stops starting new groups when the CPU total would exceed --cpu.
"""
import argparse
import hashlib
import itertools
import json
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L  # noqa: E402

p = L.p
J = L.J
I7 = L.I7
mmul = L.mmul
mpow = L.mpow
WCLQ = os.path.join(HERE, 'wclq2')
WORK = os.path.join(HERE, 'work')
GENS = os.path.join(HERE, 'gens')
RUNLOG = os.path.join(HERE, 'runlog.jsonl')
BEST_IDX = os.path.join(HERE, 'best_idx.txt')
BEST_GEN = os.path.join(HERE, 'best_gen.txt')
BEST_W = os.path.join(HERE, 'best_weight.txt')
SEED720_GEN = os.path.join(HERE, 'seed720_gen.txt')
SEED720_IDX = os.path.join(HERE, 'seed720_idx.txt')


def cpu_total():
    t = os.times()
    return t.user + t.system + t.children_user + t.children_system


def divisors_of(m):
    return [d for d in range(1, m + 1) if m % d == 0]


def nondeg_in(rng, F, k):
    """k vectors (rows) spanning a non-degenerate k-dim subspace of the span of the rows of F."""
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
    """V = E_1 + ... + E_r orthogonal (B-orthogonal blocks), E_i non-degenerate of dimension dims[i] (rows = basis)."""
    blocks = []
    F = np.eye(7, dtype=np.int64)
    for d in dims[:-1]:
        E = nondeg_in(rng, F, d)
        blocks.append(E)
        M = (F @ J @ E.T) % p                     # M[i, j] = B(F_i, E_j)
        N = L.nullspace_mod(M.T % p)              # coefficient vectors c with c @ M = 0: complement inside F
        F = (N @ F) % p
    blocks.append(F)
    assert sum(b.shape[0] for b in blocks) == 7
    return blocks


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


def read_gens(path):
    blocks = []
    for line in open(path):
        if line.startswith('# generator'):
            blocks.append([])
        elif line.strip() and not line.startswith('#') and blocks:
            blocks[-1].append(list(map(int, line.split())))
    return [np.array(b, dtype=np.int64) for b in blocks]


def closure(gens_ij, mod):
    S = {(0, 0)}
    frontier = [(0, 0)]
    while frontier:
        x = frontier.pop()
        for g in gens_ij:
            y = ((x[0] + g[0]) % mod[0], (x[1] + g[1]) % mod[1])
            if y not in S:
                S.add(y)
                frontier.append(y)
    return frozenset(S)


def sub720_groups():
    """all non-trivial subgroups of <a> x <b> (a order 15, b order 5): cyclic ones from one element, the others from
    two elements.  Returns dicts with the generator matrices a^i b^j (a, b commute)."""
    a, b = read_gens(SEED720_GEN)
    oa, ob = L.order_of(a), L.order_of(b)
    assert (oa, ob) == (15, 5), (oa, ob)
    mod = (15, 5)
    elems = [(i, j) for i in range(15) for j in range(5) if (i, j) != (0, 0)]
    subs = {}
    for x in elems:
        subs.setdefault(closure([x], mod), [x])
    for x in elems:
        for y in elems:
            H = closure([x, y], mod)
            if H not in subs:
                subs[H] = [x, y]
    out = []
    for H, gens_ij in sorted(subs.items(), key=lambda kv: (len(kv[0]), sorted(kv[0]))):
        mats = [mmul(mpow(a, i), mpow(b, j)) for (i, j) in gens_ij]
        desc = (f'subgroup of <a> x <b> of order {len(H)} (|a|=15, |b|=5) generated by '
                + ' and '.join(f'a^{i} b^{j}' for (i, j) in gens_ij))
        out.append(dict(mode='sub720', dims=[5, 2], orders=[len(H)], desc=desc, gens=mats, warm=True))
    return out


def block_samples(rng, dims, perdraw, dmin, dmax):
    while True:
        blocks = orth_blocks(rng, dims)
        elems = []
        for E in blocks:
            while True:
                g = L.rand_refl_in(rng, E, int(rng.integers(2, 9)))
                o = L.order_of(g)
                if o >= 2:
                    break
            elems.append((g, o))
        opts = []
        for g, o in elems:
            opts.append([1] + [d for d in divisors_of(o) if d > 1])
        combos = []
        for combo in itertools.product(*opts):
            nt = sum(1 for d in combo if d > 1)
            m = int(np.prod(combo))
            if nt >= 2 and dmin <= m <= dmax:
                combos.append(combo)
        if not combos:
            continue
        pick = rng.permutation(len(combos))[:perdraw]
        for c in pick:
            combo = combos[c]
            gens = [mpow(g, o // d) for (g, o), d in zip(elems, combo) if d > 1]
            ords = [d for d in combo if d > 1]
            desc = (f'blocks {"+".join(map(str, dims))}: element orders {ords} on blocks of dims '
                    f'{[dm for dm, d in zip(dims, combo) if d > 1]}; block element orders {[o for _, o in elems]}')
            yield dict(mode='blocks', dims=list(dims), orders=ords, desc=desc, gens=gens,
                       elem_orders=[o for _, o in elems], warm=False)


def analyse_group(grp):
    perms = [L.perm_of(g) for g in grp['gens']]
    lab = L.orbit_labels(perms)
    sizes, rep, good = L.analyse(lab)
    fp = hashlib.sha1(L.fingerprint(sizes, good).encode()).hexdigest()[:16]
    return lab, sizes, rep, good, fp


def evaluate(grp, args, seed, analysis, init_pts):
    t_eval = time.process_time()
    lab, sizes, rep, good, fp = analysis
    K = int(good.size)
    rec = dict(mode=grp['mode'], dims=grp['dims'], orders=grp['orders'], desc=grp['desc'], fp=fp, seed=seed,
               norbits=int(sizes.size), K=K, weight=0, optimal=None, skipped=None, warm=False,
               size_hist=None)
    rec['gens_file'] = save_gens(fp, grp)
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
    ginit = os.path.join(WORK, f'{fp}_init.txt')
    L.write_graph_packed(gbin, rows, w)
    cmd = [WCLQ, gbin, str(args.texact), str(args.theur), str(seed), gclq]
    if init_pts is not None:
        labs = np.unique(lab[init_pts])
        pos = np.full(sizes.size, -1, np.int64)
        pos[good] = np.arange(K)
        gi = pos[labs]
        if np.all(gi >= 0):
            union = np.flatnonzero(np.isin(lab, labs))
            rec['warm'] = bool(union.size == init_pts.size)
            rec['warm_orbits'] = int(labs.size)
            with open(ginit, 'w') as f:
                f.write('\n'.join(map(str, gi.tolist())) + '\n')
            cmd.append(ginit)
        else:
            rec['warm'] = 'non-good orbit in init set'
    t_cl = time.process_time()
    res = subprocess.run(cmd, capture_output=True, text=True, timeout=args.texact + args.theur + 300)
    rec['cpu_clique_driver_side'] = round(time.process_time() - t_cl, 2)
    weight, opt, verts = L.read_clique(gclq)
    rec['weight'] = int(weight)
    rec['optimal'] = bool(opt)
    rec['edges_density'] = round(L.packed_density(rows), 5)
    rec['clique_stderr'] = [l for l in res.stderr.strip().splitlines()[-2:]]
    for fpath in (gbin, gclq):
        if os.path.exists(fpath):
            os.remove(fpath)
    if os.path.exists(ginit):
        os.remove(ginit)
    chosen = good[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    idx = np.flatnonzero(np.isin(lab, chosen))
    if idx.size != weight or not L.pairwise_ok(idx):
        rec['skipped'] = 'verification failed'
        return rec, None
    rec['cpu_eval'] = round(time.process_time() - t_eval, 2)
    return rec, idx


def write_best(idx, grp, weight):
    with open(BEST_IDX, 'w') as f:
        f.write(f'# {weight} points, pairwise opposite (verified by wclq2 + numpy); generators in best_gen.txt\n')
        f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    with open(BEST_GEN, 'w') as f:
        f.write(f'# {weight} points: {grp["desc"]}\n')
        for i, g in enumerate(grp['gens']):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(g))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['sub720', 'blocks'])
    ap.add_argument('--dims', default='5,2')
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--cpu', type=float, default=480.0)
    ap.add_argument('--texact', type=float, default=20.0)
    ap.add_argument('--theur', type=float, default=5.0)
    ap.add_argument('--kmax', type=int, default=6000)
    ap.add_argument('--perdraw', type=int, default=4)
    ap.add_argument('--dmin', type=int, default=10)
    ap.add_argument('--dmax', type=int, default=400)
    ap.add_argument('--maxgroups', type=int, default=10 ** 9)
    ap.add_argument('--minsave', type=int, default=700)
    ap.add_argument('--suborder', default='', help='sub720 only: comma list of subgroup orders to run')
    args = ap.parse_args()
    os.makedirs(GENS, exist_ok=True)
    os.makedirs(WORK, exist_ok=True)
    rng = np.random.default_rng(args.seed)
    seen, best_known = load_seen()
    init_pts = None
    if args.mode == 'sub720':
        init_pts = np.loadtxt(SEED720_IDX, comments='#', dtype=np.int64).reshape(-1)
        keep = {int(x) for x in args.suborder.split(',') if x}
        gen_iter = iter([g for g in sub720_groups() if not keep or g['orders'][0] in keep])
    else:
        dims = [int(x) for x in args.dims.split(',')]
        gen_iter = block_samples(rng, dims, args.perdraw, args.dmin, args.dmax)
    start = cpu_total()
    reserve = args.texact + args.theur + 30
    tried = n_eval = n_skip = 0
    best_here = 0
    while cpu_total() - start < args.cpu - reserve and tried < args.maxgroups:
        try:
            grp = next(gen_iter)
        except StopIteration:
            break
        tried += 1
        analysis = analyse_group(grp)
        fp = analysis[-1]
        if fp in seen:
            n_skip += 1
            continue
        seen.add(fp)
        rec, idx = evaluate(grp, args, args.seed * 1000 + tried, analysis, init_pts if grp.get('warm') else None)
        rec['t_cpu_total'] = round(cpu_total() - start, 1)
        with open(RUNLOG, 'a') as f:
            f.write(json.dumps(rec) + '\n')
        n_eval += 1
        print(f"[{rec['t_cpu_total']:7.1f}s] {grp['mode']} dims={rec['dims']} orders={rec['orders']} "
              f"K={rec['K']} norb={rec['norbits']} w={rec['weight']} opt={rec['optimal']} warm={rec['warm']} "
              f"skip={rec['skipped']}", flush=True)
        if idx is not None and rec['weight'] >= args.minsave:
            rec['gens_file'] = save_gens(fp, grp)
        if idx is not None and rec['weight'] > max(best_known, best_here):
            best_here = rec['weight']
            write_best(idx, grp, rec['weight'])
            with open(BEST_W, 'w') as f:
                f.write(f'{rec["weight"]}\n')
            print('NEW BEST', rec['weight'], grp['desc'], flush=True)
    print(f'done: evaluated {n_eval}, repeats {n_skip}, sampled {tried}, best this run {best_here}, '
          f'cpu {cpu_total() - start:.1f}s', flush=True)


if __name__ == '__main__':
    main()
