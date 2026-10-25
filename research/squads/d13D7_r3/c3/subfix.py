#!/usr/bin/env python3
"""Card c3 (squad round 3): fix a set F of singleton orbits (fixed points of a unipotent element u) and search the
best union of orbits compatible with all of F, by the induced subgraph of the orbit graph and wclq2.

usage: subfix.py GENSFILE FIXFILE TEXACT THEUR SEED TAG
  GENSFILE: generator file of the group (its generator 0 is used as u; group = <u>).
  FIXFILE: point indices (or 'lift0' to use the fixed points with x4 = 0 of the group's fixed set).
Total weight = |F| + weight of the clique in the candidates.  Writes work/<tag>_best.idx when verified."""
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L  # noqa: E402


def read_gens(path):
    desc, blocks = '', []
    for line in open(path):
        if line.startswith('# generator'):
            blocks.append([])
        elif line.startswith('#'):
            desc = line[1:].strip()
        elif line.strip() and blocks:
            blocks[-1].append(list(map(int, line.split())))
    return desc, [np.array(b, dtype=np.int64) for b in blocks]


def main():
    gpath, fixfile, texact, theur, seed, tag = sys.argv[1], sys.argv[2], float(sys.argv[3]), float(sys.argv[4]), \
        int(sys.argv[5]), sys.argv[6]
    desc, gens = read_gens(gpath)
    work = os.path.join(HERE, 'work')
    os.makedirs(work, exist_ok=True)
    t0 = time.time()
    lab = L.orbit_labels([L.perm_of(g) for g in gens])
    sizes, rep, good = L.analyse(lab)
    K = int(good.size)
    print(f'{tag}: {desc}; good orbits K={K}', flush=True)
    pos = np.full(sizes.size, -1, np.int64)
    pos[good] = np.arange(K)
    if fixfile == 'lift0':
        fixed_pts = np.flatnonzero(sizes[lab] == 1)
        F_pts = fixed_pts[L.P[fixed_pts][:, 4] == 0]
    else:
        F_pts = np.loadtxt(fixfile, comments='#', dtype=np.int64).reshape(-1)
    F_orb = np.unique(lab[F_pts])
    assert np.all(sizes[F_orb] == 1), 'F must consist of singleton orbits (fixed points)'
    F = pos[F_orb]
    assert np.all(F >= 0), 'a singleton is not good'
    print(f'fixed set F: {F.size} singleton orbits', flush=True)
    rows = L.compat_packed(lab, rep, good)

    def row_bits(v):
        return np.unpackbits(rows[v].view(np.uint8), bitorder='little')[:K].astype(bool)

    cand = np.ones(K, bool)
    for f in F:
        cand &= row_bits(f)
    cand[F] = False
    C = np.flatnonzero(cand)
    print(f'candidates compatible with all of F: {C.size} (weights {np.unique(sizes[good[C]])})', flush=True)
    if C.size == 0:
        print('no candidates; total', int(sizes[good[F]].sum()), flush=True)
        return
    n = C.size
    A_sub = np.stack([row_bits(c)[C] for c in C])
    w_sub = sizes[good[C]]
    sub_bin = os.path.join(work, f'{tag}_sub.bin')
    pad = (-n) % 64
    Ap = np.zeros((n, n + pad), bool)
    Ap[:, :n] = A_sub
    rows_sub = np.packbits(Ap, axis=1, bitorder='little').view('<u8')
    L.write_graph_packed(sub_bin, rows_sub, w_sub)
    out = os.path.join(work, f'{tag}_sub.clq')
    res = subprocess.run([os.path.join(HERE, 'wclq2'), sub_bin, str(texact), str(theur), str(seed), out],
                         capture_output=True, text=True)
    weight, opt, verts = L.read_clique(out)
    chosen_orb = good[C[np.array(verts, dtype=np.int64)]] if verts else np.zeros(0, np.int64)
    idx = np.concatenate([F_pts, np.flatnonzero(np.isin(lab, chosen_orb))])
    idx = np.unique(idx)
    ok = L.pairwise_ok(idx)
    total = int(idx.size)
    print(f'clique weight {weight} (optimal {opt}); total {total}; verified {ok}; wall {time.time() - t0:.1f}s',
          flush=True)
    print('stderr:', '; '.join(l for l in res.stderr.splitlines() if l.strip())[-300:], flush=True)
    if ok:
        with open(os.path.join(work, f'{tag}_best.idx'), 'w') as f:
            f.write(f'# {total} points, {tag}\n' + '\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    os.remove(sub_bin)
    os.remove(out)


if __name__ == '__main__':
    main()
