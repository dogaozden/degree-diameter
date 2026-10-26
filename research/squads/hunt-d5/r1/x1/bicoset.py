#!/usr/bin/env python3
"""Bi-coset graphs of a group G with subgroups H=<a>, K=<b> of order 2 (card x1).
Sides: right cosets Hx and Ky (n = |G|/2 each). Edge Hx ~ Ky iff x y^-1 lies in D, where D is a union of
(H,K)-double cosets H s K with |D| = 2*Delta (so every vertex has degree Delta). Well defined because HDK = D.
Usage: bicoset.py TABLE.bin DELTA SECONDS SEED [OUT]
Cost = ordered same-side pairs at distance > 4 (both sides). Cost 0 <=> diameter <= 5.
"""
import struct, sys, random, time
import numpy as np

fn, DELTA, SECONDS, SEED = sys.argv[1], int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
OUT = sys.argv[5] if len(sys.argv) > 5 else None
rng = random.Random(SEED)

data = open(fn, 'rb').read()
N = struct.unpack('<i', data[:4])[0]
T = np.frombuffer(data[4:4 + 2 * N * N], dtype='<u2').astype(np.int64).reshape(N, N)  # T[x,y] = x*y
INV = np.argmax(T == 0, axis=1)
invols = [x for x in range(1, N) if T[x, x] == 0]
assert invols, "no involution"

def setup(a, b):
    """cosets (A: Hg, B: Kg, left cosets by left multiplication) and double cosets HsK."""
    Aid = -np.ones(N, dtype=np.int64); Bid = -np.ones(N, dtype=np.int64)
    Arep, Brep = [], []
    for g in range(N):
        if Aid[g] < 0:
            Aid[g] = Aid[T[a, g]] = len(Arep); Arep.append(g)
    for g in range(N):
        if Bid[g] < 0:
            Bid[g] = Bid[T[b, g]] = len(Brep); Brep.append(g)
    dc_of = -np.ones(N, dtype=np.int64); dcs = []
    for s in range(N):
        if dc_of[s] < 0:
            els = sorted({s, T[a, s], T[s, b], T[a, T[s, b]]})
            for e in els: dc_of[e] = len(dcs)
            dcs.append(els)
    return Aid, Bid, np.array(Arep), np.array(Brep), dcs

def adjacency(D_elems, Arep, Bid):
    n = len(Arep)
    invD = INV[np.array(D_elems)]
    nb = Bid[T[invD[:, None], Arep[None, :]]]          # m x n: B-class of inv(d) * x_i
    M = np.zeros((n, n), dtype=np.float32)
    M[np.broadcast_to(np.arange(n)[None, :], nb.shape), nb] = 1.0
    return M

def cost(M):
    n = M.shape[0]
    R1 = ((M @ M.T) > 0).astype(np.float32)
    RA = ((R1 @ R1) > 0).sum()
    R2 = ((M.T @ M) > 0).astype(np.float32)
    RB = ((R2 @ R2) > 0).sum()
    return int(2 * n * n - RA - RB)

def run(a, b, n4, n2):
    Aid, Bid, Arep, Brep, dcs = setup(a, b)
    n = len(Arep)
    pool4 = [i for i, d in enumerate(dcs) if len(d) == 4]
    pool2 = [i for i, d in enumerate(dcs) if len(d) == 2]
    if len(pool4) < n4 or len(pool2) < n2: return None
    state = rng.sample(pool4, n4) + rng.sample(pool2, n2)
    pools = {4: pool4, 2: pool2}
    sizes = [4] * n4 + [2] * n2
    def elems(st): return [e for c in st for e in dcs[c]]
    cur = cost(adjacency(elems(state), Arep, Bid))
    best, best_state = cur, list(state)
    t0 = time.time(); it = 0
    while time.time() - t0 < SECONDS and best > 0:
        it += 1
        k = rng.randrange(len(state))
        pool = pools[sizes[k]]
        c = rng.choice(pool)
        if c in state: continue
        new = list(state); new[k] = c
        cn = cost(adjacency(elems(new), Arep, Bid))
        frac = (time.time() - t0) / SECONDS
        temp = 3.0 * (0.05 / 3.0) ** frac
        if cn <= cur or rng.random() < np.exp(-(cn - cur) / temp):
            state, cur = new, cn
            if cur < best: best, best_state = cur, list(state)
    return best, best_state, dcs, it, (Aid, Bid, Arep, Brep)

if __name__ == '__main__':
    # pick H=<a>, K=<b> involutions and a type (n4 size-4 double cosets, n2 size-2) with 2*n4 + n2 = Delta
    a = rng.choice(invols)
    conj = sorted(set(T[T[:, a], INV].tolist()))   # g a g^-1 for all g
    b = rng.choice(conj)
    types = [(n4, DELTA - 2 * n4) for n4 in range(0, DELTA // 2 + 1)]
    n4, n2 = rng.choice(types)
    res = run(a, b, n4, n2)
    if res is None:
        print(f"RESULT N={N} skip a={a} b={b} type={n4},{n2}"); sys.exit(0)
    best, st, dcs, it, (Aid, Bid, Arep, Brep) = res
    D = [e for c in st for e in dcs[c]]
    print(f"RESULT N={N} D={DELTA} n={N//2} a={a} b={b} type={n4},{n2} iters={it} best={best} S= {' '.join(map(str, sorted(D)))}")
    if best == 0 and OUT:
        M = adjacency(D, Arep, Bid); n = M.shape[0]
        with open(OUT + '.edges', 'w') as f:
            f.write(f"{2 * n}\n")
            for i, j in zip(*np.nonzero(M)): f.write(f"{i} {n + j}\n")
        print(f"WROTE {OUT}.edges")
