#!/usr/bin/env python3
"""c5: search for large cliques of G that are unions of orbits of a group H <= F_11^* x O(D) (similitudes with square
multiplier, so H acts by automorphisms of G).  Usage: sym_search.py SEED TRIALS CPU_LIMIT [mode]
Prints one line per evaluated group; writes best clique (vertex list, s b c f) to c5/best_vertices_<seed>.txt."""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import symlib as L

HERE = os.path.dirname(os.path.abspath(__file__))
rng = np.random.default_rng(1)
T0 = time.process_time()


def wnorm(w):
    return int(np.asarray(w) @ L.M @ np.asarray(w)) % L.q


def rand_sim(maxlen=12):
    A = L.I4.copy()
    for _ in range(int(rng.integers(2, maxlen))):
        while True:
            w = rng.integers(0, 11, size=4)
            if wnorm(w) != 0:
                break
        A = (A @ L.reflection(w)) % 11
    lam = int(rng.integers(1, 11))
    return (lam * A) % 11


def evaluate(gens, tag, greedy_iters=200, exact_limit=160):
    perms = [L.perm_affine(A) for A in gens]
    oid = L.orbit_labels(perms)
    norb = int(oid.max()) + 1
    sizes = np.bincount(oid)
    order = np.argsort(oid, kind='stable')
    starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    good = []
    reps = {}
    for k in range(norb):
        mem = order[starts[k]:starts[k] + sizes[k]]
        r = int(mem[0])
        if sizes[k] == 1:
            good.append(k); reps[k] = r; continue
        row = L.adjrow(r)
        if row[mem[1:]].all():
            good.append(k); reps[k] = r
    ng = len(good)
    if ng == 0:
        return 0, None, (norb, 0, 0)
    gidx = {k: i for i, k in enumerate(good)}
    Cm = np.zeros((ng, ng), dtype=bool)
    for k in good:
        row = L.adjrow(reps[k])
        cnt = np.bincount(oid[~row], minlength=norb)
        ok = (cnt == 0)
        i = gidx[k]
        Cm[i, :] = ok[good]
    Cm[np.arange(ng), np.arange(ng)] = False
    Cm = Cm & Cm.T
    w = sizes[good].astype(np.int64)
    if ng <= exact_limit:
        bw, bset, complete = L.exact_max_weight_clique(Cm, w, time_nodes=300000)
        tag2 = 'exact' if complete else 'exact-partial'
    else:
        bw, bset = L.weighted_greedy(Cm, w, rng, greedy_iters, noise=0.3)
        tag2 = 'greedy'
    verts = []
    for i in bset:
        k = good[i]
        verts.extend(order[starts[k]:starts[k] + sizes[k]].tolist())
    verts = sorted(verts)
    print(f'{tag} norb={norb} good={ng} best_weight={bw} ({tag2})', flush=True)
    return bw, verts, (norb, ng, len(bset))


if __name__ == '__main__':
    seed, trials, cpu_limit = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    mode = sys.argv[4] if len(sys.argv) > 4 else 'mixed'
    rng = np.random.default_rng(seed)
    best = 0
    t_start = time.process_time()
    results = []
    for t in range(trials):
        if time.process_time() - T0 > cpu_limit:
            print('CPU limit reached', flush=True)
            break
        kind = mode
        if kind == 'mixed':
            kind = 'cyc' if t % 3 else 'two'
        if kind == 'cyc':
            A = rand_sim()
            d = L.matpow_order(A, 400)
            if d is None or d < 2:
                continue
            gens = [A]
            tag = f'cyc d={d}'
        else:
            A = rand_sim(); B = rand_sim()
            gens = [A, B]
            tag = f'two dA={L.matpow_order(A,400)} dB={L.matpow_order(B,400)}'
        bw, verts, info = evaluate(gens, tag)
        if verts is not None and bw > best:
            best = bw
            np.save(os.path.join(HERE, f'best_verts_seed{seed}.npy'), np.array(verts))
            with open(os.path.join(HERE, f'best_verts_seed{seed}.txt'), 'w') as f:
                f.write(f'# clique size {bw} (incl. 0 after translation not applied), group {tag}\n')
                for v in verts:
                    f.write(' '.join(map(str, L.C[v].tolist())) + '\n')
            print(f'  NEW BEST {bw}', flush=True)
    print('done best', best, 'cpu', round(time.process_time() - T0, 1), flush=True)
