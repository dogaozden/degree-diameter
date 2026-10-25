#!/usr/bin/env python3
"""Rebuild the orbit graph of a saved group and read the clique written by wclq2 (refine.py): recover.py FP CLQ."""
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbq13 as L  # noqa: E402

fp, clq = sys.argv[1], sys.argv[2]
rows = [list(map(int, ln.split())) for ln in open(os.path.join(HERE, 'gens', fp + '.txt'))
        if ln.strip() and not ln.startswith('#')]
mats = [np.array(rows[i:i + 7], dtype=np.int64) for i in range(0, len(rows), 7)]
lab = L.orbit_labels([L.perm_of(g) for g in mats])
sizes, rep, good = L.analyse(lab)
weight, opt, verts = L.read_clique(clq)
chosen = good[np.array(verts, dtype=np.int64)]
idx = np.flatnonzero(np.isin(lab, chosen))
ok = idx.size == weight and L.pairwise_ok(idx)
print('weight', weight, 'idx', idx.size, 'verified', ok, flush=True)
if ok:
    with open(os.path.join(HERE, 'best_idx.txt'), 'w') as f:
        f.write(f'# {idx.size} points, pairwise opposite in H(13) (verified by numpy); group gens/{fp}.txt\n')
        f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    with open(os.path.join(HERE, 'best_gen.txt'), 'w') as f:
        f.write(f'# {idx.size} points: gens/{fp}.txt (k=5, a of order 12 on U, b of order 3 on U-perp, |a|=12, |b|=12)\n')
        f.write(open(os.path.join(HERE, 'gens', fp + '.txt')).read())
    with open(os.path.join(HERE, 'best_weight.txt'), 'w') as f:
        f.write(f'{idx.size}\n')
