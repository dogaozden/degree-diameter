#!/usr/bin/env python3
"""Card c2 (squad round 6): helpers for the warm-started subgroup search.  Uses orbl.py (copied from round 4)."""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L  # noqa: E402

R4 = '/home/user/degree-diameter/research/squads/d13D7_r4/c1'
MMUL = L.mmul
MPOW = L.mpow


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


def write_gens(path, desc, mats):
    with open(path, 'w') as f:
        f.write(f'# {desc}\n')
        for i, m in enumerate(mats):
            f.write(f'# generator {i}\n')
            f.write(L.mat_to_text(m))


def read_points(path):
    return np.loadtxt(path, comments='#', dtype=np.int64).reshape(-1)


def a_b():
    """a (order 15 on the 5-dim block U) and b (order 5 on U-perp) from the round-4 seed; they commute."""
    _, (a, b) = read_gens(os.path.join(R4, 'seed720_gen.txt'))
    assert (L.order_of(a), L.order_of(b)) == (15, 5)
    assert np.array_equal(MMUL(a, b), MMUL(b, a))
    return a, b


def h_matrix():
    a, b = a_b()
    return MMUL(a, MPOW(b, 2))


def orbit_graph(g, pts, tag, workdir):
    """orbit graph of <g>: returns (gbin path, lab, sizes, rep, good, init-file path or None, init weight)."""
    lab = L.orbit_labels([L.perm_of(g)])
    sizes, rep, good = L.analyse(lab)
    K = int(good.size)
    pos = np.full(sizes.size, -1, np.int64)
    pos[good] = np.arange(K)
    init_path, init_w = None, None
    if pts is not None:
        labs = np.unique(lab[pts])
        gi = pos[labs]
        if np.any(gi < 0):
            raise SystemExit('init set uses a non-good orbit')
        union = np.flatnonzero(np.isin(lab, labs))
        is_union = union.size == pts.size and np.array_equal(np.sort(union), np.sort(pts))
        print(f'init set: {pts.size} points = union of {labs.size} orbits: {is_union}', flush=True)
        if not is_union:
            raise SystemExit('init set is not a union of orbits')
        init_path = os.path.join(workdir, f'{tag}_init.txt')
        with open(init_path, 'w') as f:
            f.write('\n'.join(map(str, gi.tolist())) + '\n')
        init_w = int(sizes[labs].sum())
    return lab, sizes, rep, good, init_path, init_w
