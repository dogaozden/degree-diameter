#!/usr/bin/env python3
"""Card c3 (squad round 3): rebuild a saved group from its generator file (gens/<fp>.txt) and re-solve its orbit
clique problem with other limits or seeds.  usage: replay.py GENSFILE TEXACT THEUR SEED [SEED ...]
Writes replay_<fp>_<seed>.idx (point indices) for every run that improves on the best of this replay, and prints
one line per run: weight, optimal flag, verification of the union (pairwise opposite)."""
import os
import subprocess
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import orbl as L  # noqa: E402

WCLQ = os.path.join(HERE, 'wclq')


def read_gens(path):
    desc, blocks, cur = '', [], None
    for line in open(path):
        if line.startswith('# generator'):
            cur = []
            blocks.append(cur)
        elif line.startswith('#'):
            desc = line[1:].strip()
        elif line.strip() and cur is not None:
            cur.append(list(map(int, line.split())))
    return desc, [np.array(b, dtype=np.int64) for b in blocks]


def main():
    gpath, texact, theur = sys.argv[1], float(sys.argv[2]), float(sys.argv[3])
    seeds = [int(s) for s in sys.argv[4:]] or [1]
    desc, gens = read_gens(gpath)
    fp = os.path.splitext(os.path.basename(gpath))[0]
    lab = L.orbit_labels([L.perm_of(g) for g in gens])
    sizes, rep, good = L.analyse(lab)
    K = good.size
    print(f'{fp}: {desc}; good orbits K={K}', flush=True)
    A = L.compat(lab, rep, good)
    w = sizes[good]
    gbin = os.path.join(HERE, 'work', f'replay_{fp}.bin')
    os.makedirs(os.path.dirname(gbin), exist_ok=True)
    L.write_graph(gbin, A, w)
    best = 0
    for s in seeds:
        out = os.path.join(HERE, 'work', f'replay_{fp}_{s}.clq')
        t = time.time()
        subprocess.run([WCLQ, gbin, str(texact), str(theur), str(s), out], capture_output=True, text=True)
        weight, opt, verts = L.read_clique(out)
        chosen = good[np.array(verts, dtype=np.int64)]
        idx = np.flatnonzero(np.isin(lab, chosen))
        ok = idx.size == weight and L.pairwise_ok(idx)
        print(f'seed {s}: weight {weight} optimal {opt} verified {ok} wall {time.time() - t:.1f}s', flush=True)
        if ok and weight > best:
            best = weight
            with open(os.path.join(HERE, 'work', f'replay_{fp}_best.idx'), 'w') as f:
                f.write(f'# {weight} points from {fp}\n' + '\n'.join(map(str, np.sort(idx).tolist())) + '\n')
        os.remove(out)
    os.remove(gbin)


if __name__ == '__main__':
    main()
