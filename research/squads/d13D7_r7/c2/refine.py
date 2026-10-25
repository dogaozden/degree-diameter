#!/usr/bin/env python3
"""Re-run wclq2 (local search) on a saved group: refine.py FP THEUR SEED.  Rebuilds the orbit graph from gens/FP.txt."""
import os
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbq13 as L  # noqa: E402

fp, theur, seed = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
rows = [list(map(int, ln.split())) for ln in open(os.path.join(HERE, 'gens', fp + '.txt'))
        if ln.strip() and not ln.startswith('#')]
mats = [np.array(rows[i:i + 7], dtype=np.int64) for i in range(0, len(rows), 7)]
lab = L.orbit_labels([L.perm_of(g) for g in mats])
sizes, rep, good = L.analyse(lab)
print('K', good.size, 'norb', sizes.size, flush=True)
crows = L.compat_packed(lab, rep, good)
w = sizes[good]
gbin = os.path.join(HERE, 'work', f'refine_{fp}.bin')
gclq = os.path.join(HERE, 'work', f'refine_{fp}.clq')
os.makedirs(os.path.join(HERE, 'work'), exist_ok=True)
L.write_graph_packed(gbin, crows, w)
subprocess.run([os.path.join(HERE, 'wclq2'), gbin, '1', str(theur), str(seed), gclq], capture_output=True, text=True,
               timeout=int(theur) + 300)
weight, opt, verts = L.read_clique(gclq)
chosen = good[np.array(verts, dtype=np.int64)]
idx = np.flatnonzero(np.isin(lab, chosen))
ok = idx.size == weight and L.pairwise_ok(idx)
print('REFINE weight', weight, 'optimal', opt, 'verified', ok, flush=True)
if ok:
    out = os.path.join(HERE, 'refined_idx.txt')
    with open(out, 'w') as f:
        f.write(f'# {weight} points, pairwise opposite (verified), group gens/{fp}.txt\n')
        f.write('\n'.join(map(str, np.sort(idx).tolist())) + '\n')
    print('wrote', out)
os.remove(gbin)
