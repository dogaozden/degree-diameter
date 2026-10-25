#!/usr/bin/env python3
"""Card c3 (squad round 3): the Eichler class E = E(e4, 5e1+e5) of order 11 (Jordan type (3,1^4), 1343 fixed points),
in closed form, without building the full orbit graph.

Chart: affine points (1, a, b, c, c^2 - a e - b f, e, f).  E acts on the chart as translation by u' = (5,0,0,1,0), so
the 14641 affine orbits (lines) are the cosets t + F u'.  Each coset has a unique representative with e = 0:
t = (a, b, c, 0, f).
* Two lines t, s are compatible iff Q'(t - s + lam u') != 0 for all lam, Q'(a,b,c,e,f) = c^2 - ae - bf.  For
  d = t - s = (a,b,c,0,f): Q'(d + lam u') = c^2 - (a+5 lam) lam - b f, so compatibility is the test "5 lam^2 + a lam
  + (bf - c^2) has no root mod 11" (a function of d only: a Cayley graph on F_11^4).
* A fixed point (point at infinity) z with z1 + 5 z5 = 0 (these are the 1343 fixed points) is compatible with the line
  t iff n_z . t + z4 != 0, where n_z = (z5, z6, -2 z3, z1, z2) and n_z . t = z5 a + z6 b - 2 z3 c + z2 f (e = 0).
So for a set F of fixed points, the candidate lines are the cosets avoiding all these affine hyperplanes, and the best
union with F is |F| + 11 * (clique number of the induced Cayley subgraph on the candidates).

usage: fastlift.py FIXSET TEXACT THEUR SEED TAG [--check-397]
  FIXSET: point-index file of fixed points of E (the 122 singletons), or 'lift0' (the fixed points with x4 = 0)
          or 'from397' (fixed points of the 397 set: seed397_r2c6_idx.txt), as the singleton part.
Writes work/<tag>_best.idx (verified point set) when the union is valid."""
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L  # noqa: E402

p = 11
I11 = np.arange(p)
Q_E = np.array([5, 0, 0, 1, 0])          # u'


def coset_code(a, b, c, f):
    return ((a % p) * 1331 + (b % p) * 121 + (c % p) * 11 + (f % p))


def decode(code):
    return code // 1331, (code // 121) % 11, (code // 11) % 11, code % 11


def compat_table():
    """boolean table over codes of d = (a,b,c,f): True iff the lines t and t + d are compatible."""
    tab = np.zeros(11 ** 4, bool)
    for code in range(11 ** 4):
        a, b, c, f = decode(code)
        const = (b * f - c * c) % p
        roots = False
        for lam in range(p):
            if (5 * lam * lam + a * lam + const) % p == 0:
                roots = True
                break
        tab[code] = not roots
    return tab


def singletons_from_points(idx):
    """(n_z (5,), z4) for each fixed point z of E given by point index."""
    Z = L.P[idx]
    n = np.stack([Z[:, 5], Z[:, 6], (-2 * Z[:, 3]) % p, Z[:, 1], Z[:, 2]], axis=1) % p
    return n, Z[:, 4] % p


def forbidden_mask(nz, z4):
    """boolean over all 11^4 coset codes: True iff the line is blocked by some singleton."""
    codes = np.arange(11 ** 4)
    a, b, c, f = decode(codes)
    blocked = np.zeros(11 ** 4, bool)
    for n, k in zip(nz, z4):
        val = (n[0] * a + n[1] * b + n[2] * c + n[4] * f + k) % p   # n . t + z4, e = 0 so n_e drops out
        blocked |= (val == 0)
    return blocked


def line_point_indices(a, b, c, f):
    """the 11 point indices of the line with coset rep (a,b,c,0,f): offsets (a,b,c,lam,f) with lam free."""
    pts = []
    for lam in range(p):
        aa, ee = (a + 5 * lam) % p, lam
        x4 = (c * c - aa * ee - b * f) % p
        pts.append([1, aa, b % p, c % p, x4, ee, f % p])
    pts = np.array(pts, dtype=np.int64)
    codes = pts @ L.PW
    idx = np.searchsorted(L.CODES, codes)
    assert np.array_equal(L.CODES[idx], codes)
    return idx


def main():
    fixset, texact, theur, seed, tag = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    t0 = time.time()
    # fixed points of E: points with x0 = 0 and z1 + 5 z5 = 0 (and on Q; all points of Q with x0=0 satisfying this)
    Z_all = L.P
    fixed_mask = (Z_all[:, 0] == 0) & ((Z_all[:, 1] + 5 * Z_all[:, 5]) % p == 0)
    fixed_all = np.flatnonzero(fixed_mask)
    if fixset == 'lift0':
        F = fixed_all[Z_all[fixed_all, 4] == 0]
    elif fixset == 'from397':
        idx397 = np.loadtxt(os.path.join(HERE, 'seed397_r2c6_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
        F = np.intersect1d(idx397, fixed_all)
    else:
        F = np.loadtxt(fixset, comments='#', dtype=np.int64).reshape(-1)
    print(f'{tag}: singletons |F| = {F.size} (fixed points of E: {fixed_all.size})', flush=True)
    nz, z4 = singletons_from_points(F)
    blocked = forbidden_mask(nz, z4)
    cand = np.flatnonzero(~blocked)
    print(f'candidate lines (cosets) avoiding all singletons: {cand.size}', flush=True)
    table = compat_table()
    a, b, c, f = decode(cand)
    n = cand.size
    # adjacency: code of t_i - t_j (componentwise mod 11) indexes the table
    A = np.zeros((n, n), bool)
    for i in range(n):
        d = coset_code(a[i] - a, b[i] - b, c[i] - c, f[i] - f)
        A[i] = table[d]
    np.fill_diagonal(A, False)
    print(f'compat density among candidates: {A.sum() / max(1, n * (n - 1)):.4f}', flush=True)
    # sanity: the 397 set's lines are cliques of this model (only when checking the 397 lifts)
    if fixset == 'from397':
        idx397 = np.loadtxt(os.path.join(HERE, 'seed397_r2c6_idx.txt'), comments='#', dtype=np.int64).reshape(-1)
        affine = idx397[Z_all[idx397, 0] == 1]
        P_aff = Z_all[affine]
        reps = set()
        for x in P_aff:
            aa, bb, cc, ee, ff = x[1], x[2], x[3], x[5], x[6]
            lam = (-ee) % p
            reps.add(coset_code(aa + 5 * lam, bb, cc, ff))
        reps = sorted(reps)
        pos_c = {int(cc_): i for i, cc_ in enumerate(cand.tolist())}
        ok_c = all(r in pos_c for r in [int(r) for r in reps] if True)
        print('397 lines: cosets', len(reps), 'all candidates:', all((int(np.flatnonzero(cand == r)[0]) if np.any(cand == r) else -1) >= 0 for r in reps), flush=True)
        ids = [int(np.flatnonzero(cand == r)[0]) for r in reps if np.any(cand == r)]
        clique_ok = all(A[i, j] for i in ids for j in ids if i != j)
        print('397 lines pairwise compatible in the model:', clique_ok, 'count', len(ids), flush=True)
    rows_n = n
    pad = (-rows_n) % 64
    Ap = np.zeros((rows_n, rows_n + pad), bool)
    Ap[:, :rows_n] = A
    rows = np.packbits(Ap, axis=1, bitorder='little').view('<u8')
    work = os.path.join(HERE, 'work')
    os.makedirs(work, exist_ok=True)
    gbin = os.path.join(work, f'{tag}_fl.bin')
    L.write_graph_packed(gbin, rows, np.full(n, 11, np.int64))
    out = os.path.join(work, f'{tag}_fl.clq')
    res = subprocess.run([os.path.join(HERE, 'wclq2'), gbin, str(texact), str(theur), str(seed), out],
                         capture_output=True, text=True)
    weight, opt, verts = L.read_clique(out)
    k = weight // 11
    chosen = cand[np.array(verts, dtype=np.int64)] if verts else np.zeros(0, np.int64)
    pts = [F]
    for code in chosen.tolist():
        a_, b_, c_, f_ = decode(np.array([code]))
        pts.append(line_point_indices(int(a_[0]), int(b_[0]), int(c_[0]), int(f_[0])))
    idx = np.unique(np.concatenate(pts))
    valid = L.pairwise_ok(idx)
    print(f'lines k = {k} (optimal {opt}); total {idx.size}; verified {valid}; wall {time.time() - t0:.1f}s', flush=True)
    print('stderr:', '; '.join(l for l in res.stderr.splitlines() if l.strip())[-300:], flush=True)
    if valid:
        with open(os.path.join(work, f'{tag}_best.idx'), 'w') as fh:
            fh.write(f'# {idx.size} points, {tag}\n' + '\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    os.remove(gbin)
    os.remove(out)


if __name__ == '__main__':
    main()
