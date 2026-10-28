"""lift9.py: the D = 9 ball lift of H(q) (Theorem 2 of POLYGON_LEVELS.md), written as an edge list.

Input: a point colouring and a line colouring of H(q) by k colours (int32 files, -1 = uncoloured), in which every
colour class is dominating (meets every 2-ball). The builder
  1. completes both colourings to partitions A_0..A_{k-1} (points) and B_0..B_{k-1} (lines) with |A_i| = |B_i|,
     keeping every coloured element in its class (needs sum_i max(|D_i|, |E_i|) <= N);
  2. takes r bijections sigma_t: P -> L with sigma_t(A_i) = B_i (random inside each class, seed-dependent);
  3. lifts I(H(q)) + sigma_1..sigma_r over Z_m, m = 2rk+1: vertex (v, g) has id g*2N + v (points 0..N-1, lines
     N..2N-1); edges (p,g)-(l,g) for p on l and (z,g)-(sigma_t(z), g + t*k + i + 1) for z in A_i.
Usage: python3 lift9.py HEXBIN POINTCLS LINECLS k r seed OUT.edges
"""
import sys
import numpy as np
from hexlib import Hex


def complete(cls_p, cls_l, k, N, rng):
    cp, cl = cls_p.copy(), cls_l.copy()
    sp = np.bincount(cp[cp >= 0], minlength=k)
    sl = np.bincount(cl[cl >= 0], minlength=k)
    target = np.maximum(sp, sl)
    if target.sum() > N:
        raise SystemExit(f'cannot balance: sum max sizes {target.sum()} > N {N}')
    extra = N - target.sum()
    for i in range(extra):
        target[i % k] += 1
    for arr, s in ((cp, sp), (cl, sl)):
        free = np.where(arr < 0)[0]
        rng.shuffle(free)
        pos = 0
        for i in range(k):
            need = target[i] - (arr == i).sum()
            arr[free[pos:pos + need]] = i
            pos += need
        assert (arr >= 0).all()
    return cp, cl


def main():
    hexbin, fp, fl, k, r, seed, out = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), \
        int(sys.argv[6]), sys.argv[7]
    H = Hex(hexbin)
    N = H.N
    rng = np.random.default_rng(seed)
    cp, cl = complete(np.fromfile(fp, dtype=np.int32).astype(np.int64),
                      np.fromfile(fl, dtype=np.int32).astype(np.int64), k, N, rng)
    m = 2 * r * k + 1
    sig = []
    for t in range(r):
        s = np.empty(N, dtype=np.int64)
        for i in range(k):
            P = np.where(cp == i)[0]
            L = np.where(cl == i)[0]
            rng.shuffle(L)
            s[P] = L
        sig.append(s)
    n2 = 2 * N
    edges = []
    for g in range(m):
        base = g * n2
        for l in range(N):
            for p in H.lines[l]:
                edges.append((base + p, base + N + l))
        for t in range(r):
            for z in range(N):
                h = (g + t * k + cp[z] + 1) % m
                edges.append((base + z, h * n2 + N + sig[t][z]))
    with open(out, 'w') as f:
        f.write(f'{m * n2}\n')
        f.write('\n'.join(f'{a} {b}' for a, b in edges))
        f.write('\n')
    print(f'q={H.q} k={k} r={r} m={m}: {m * n2} vertices, degree {H.q + 1 + r}, {len(edges)} edges -> {out}')


if __name__ == '__main__':
    main()
