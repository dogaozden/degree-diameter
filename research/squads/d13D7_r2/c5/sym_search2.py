#!/usr/bin/env python3
"""c5: symmetric clique search, driver. Groups: cyclic subgroups <A^(m/k)> (powers of random similitudes A of order m,
so small orders are reached) and two-generator groups <X,Y> with closure of at most LIM elements.
usage: sym_search2.py SEED CPU_LIMIT"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
import symlib as L
import sym_search as S

seed, cpu_limit = int(sys.argv[1]), float(sys.argv[2])
S.rng = np.random.default_rng(seed)
LIM = 200
T0 = time.process_time()


def mpow(A, e):
    R = L.I4.copy()
    B = A.copy()
    while e:
        if e & 1:
            R = (R @ B) % 11
        B = (B @ B) % 11
        e >>= 1
    return R


def closure(gens, limit=LIM):
    elems = {L.I4.tobytes(): L.I4}
    frontier = [L.I4]
    while frontier:
        new = []
        for X in frontier:
            for g in gens:
                Y = (X @ g) % 11
                key = Y.tobytes()
                if key not in elems:
                    elems[key] = Y
                    new.append(Y)
                    if len(elems) > limit:
                        return None
        frontier = new
    return len(elems)


def divisors(m):
    return [k for k in range(2, m + 1) if m % k == 0]


best = 0
t = 0
seen = set()
while time.process_time() - T0 < cpu_limit:
    t += 1
    A = S.rand_sim()
    m = L.matpow_order(A, 400)
    if m is None or m < 2:
        continue
    pool = []
    for k in divisors(m):
        if k > 60:
            continue
        X = mpow(A, m // k)
        d = L.matpow_order(X, 400)
        if d != k:
            continue
        key = (k, X.tobytes())
        pool.append(X)
        # cyclic group <X>: skip exact duplicates
        if (k, min(mpow(X, j).tobytes() for j in range(1, k))) in seen:
            continue
        seen.add((k, min(mpow(X, j).tobytes() for j in range(1, k))))
        bw, verts, info = S.evaluate([X], f'cyc k={k} m={m}')
        if verts is not None and bw > best:
            best = bw
            np.save(os.path.join(S.HERE, f'best_verts_seed{seed}.npy'), np.array(verts))
            with open(os.path.join(S.HERE, f'best_verts_seed{seed}.txt'), 'w') as f:
                f.write(f'# clique size {bw}; group <X>, order {k}, X = {X.tolist()}\n')
                for v in verts:
                    f.write(' '.join(map(str, L.C[v].tolist())) + '\n')
            print(f'  NEW BEST {bw}', flush=True)
    # two-generator groups from the pool
    if len(pool) >= 2 and time.process_time() - T0 < cpu_limit:
        i, j = S.rng.integers(0, len(pool), size=2)
        if i != j:
            X, Y = pool[i], pool[j]
            n = closure([X, Y])
            if n is not None and n >= 4:
                bw, verts, info = S.evaluate([X, Y], f'two |H|={n}')
                if verts is not None and bw > best:
                    best = bw
                    np.save(os.path.join(S.HERE, f'best_verts_seed{seed}.npy'), np.array(verts))
                    with open(os.path.join(S.HERE, f'best_verts_seed{seed}.txt'), 'w') as f:
                        f.write(f'# clique size {bw}; two-generator group |H|={n}\n')
                        for v in verts:
                            f.write(' '.join(map(str, L.C[v].tolist())) + '\n')
                    print(f'  NEW BEST {bw}', flush=True)
print('done best', best, 'trials', t, 'cpu', round(time.process_time() - T0, 1), flush=True)
