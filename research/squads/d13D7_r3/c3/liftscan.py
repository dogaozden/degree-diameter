#!/usr/bin/env python3
"""Card c3 (squad round 3): neighbourhood scan over the lift constants of the 122 singletons of the Eichler class E.

Model (see fastlift.py): singleton b (one per base point of the elliptic quadric; 122 of them) with normal m_b in F^4
(coefficients of a, b, c, f) and constant k_b (its z4) blocks the coset t = (a,b,c,0,f) iff m_b . t + k_b = 0.
For a lift vector k, the candidate lines are the cosets not blocked by any singleton; the best union is 122 + 11 * w,
where w = clique number of the induced subgraph of the Cayley graph on the candidates.

usage: liftscan.py TEXACT SEED [MAXCAND]   (scans all single changes k_b -> k' of the 397 lift)"""
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L  # noqa: E402
import fastlift as F_  # noqa: E402

p = 11
TABLE = F_.compat_table()


def base_data(points):
    Z = L.P[points]
    m = np.stack([Z[:, 5], Z[:, 6], (-2 * Z[:, 3]) % p, Z[:, 2]], axis=1) % p   # (n_a, n_b, n_c, n_f) on (a,b,c,f)
    k = Z[:, 4] % p
    return m, k


def all_cosets():
    codes = np.arange(p ** 4)
    a, b, c, f = F_.decode(codes)
    return codes, np.stack([a, b, c, f], axis=1)


def candidates(m, k, T):
    """codes of the unblocked cosets for the singleton set (m, k)."""
    blocked = np.zeros(T.shape[0], bool)
    for mb, kb in zip(m, k):
        blocked |= ((T @ mb + kb) % p == 0)
    return np.flatnonzero(~blocked)


def clique_on(cand_codes, texact, theur, seed, tag):
    """max-weight (unit weight 11) clique among the candidate cosets; returns (w, list of codes)."""
    n = cand_codes.size
    if n == 0:
        return 0, []
    a, b, c, f = F_.decode(cand_codes)
    d = F_.coset_code(a[:, None] - a[None, :], b[:, None] - b[None, :], c[:, None] - c[None, :],
                      f[:, None] - f[None, :])
    A = TABLE[d]
    np.fill_diagonal(A, False)
    pad = (-n) % 64
    Ap = np.zeros((n, n + pad), bool)
    Ap[:, :n] = A
    rows = np.packbits(Ap, axis=1, bitorder='little').view('<u8')
    gbin = os.path.join(HERE, 'work', f'{tag}.bin')
    out = os.path.join(HERE, 'work', f'{tag}.clq')
    os.makedirs(os.path.join(HERE, 'work'), exist_ok=True)
    L.write_graph_packed(gbin, rows, np.full(n, 11, np.int64))
    subprocess.run([os.path.join(HERE, 'wclq2'), gbin, str(texact), str(theur), str(seed), out],
                   capture_output=True, text=True)
    w, opt, verts = L.read_clique(out)
    os.remove(gbin)
    os.remove(out)
    return w // 11, [int(cand_codes[v]) for v in verts], opt


def main():
    texact = float(sys.argv[1])
    seed = int(sys.argv[2])
    idx397 = np.loadtxt(os.path.join(HERE, 'seed397_r2c6_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
    fixed_all = np.flatnonzero((L.P[:, 0] == 0) & ((L.P[:, 1] + 5 * L.P[:, 5]) % p == 0))
    S = np.intersect1d(idx397, fixed_all)
    m, k = base_data(S)
    codes, T = all_cosets()
    t0 = time.time()
    base_cand = candidates(m, k, T)
    w0, cl0, opt0 = clique_on(base_cand, texact, 0, seed, 'scan_base')
    print(f'base (397 lift): candidates {base_cand.size}, clique {w0} (optimal {opt0}), total {122 + 11 * w0}',
          flush=True)
    best = (w0, None)
    results = []
    for bi in range(len(k)):
        for newk in range(p):
            if newk == k[bi]:
                continue
            k2 = k.copy()
            k2[bi] = newk
            cand = candidates(m, k2, T)
            if cand.size == 0:
                results.append((0, cand.size, bi, newk))
                continue
            w, cl, opt = clique_on(cand, texact, 0, seed, 'scan')
            results.append((w, cand.size, bi, newk))
            if w > best[0]:
                best = (w, (bi, newk))
                print(f'  improving single change: base {bi} k {k[bi]} -> {newk}: candidates {cand.size}, '
                      f'clique {w} (optimal {opt}), total {122 + 11 * w}', flush=True)
    results.sort(reverse=True)
    print('top single changes (clique, candidates, base, newk):', results[:8], flush=True)
    from collections import Counter
    print('histogram of clique values over all single changes:', sorted(Counter(r[0] for r in results).items()),
          flush=True)
    print(f'scan done in {time.time() - t0:.1f}s; best single-change clique {best[0]}', flush=True)


if __name__ == '__main__':
    main()
