# Independent recomputation of the hx cost for a few hit sets (numpy BFS, no hx code), c3 sanity check.
import sys, glob, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/deep-49/tools')
import meta
def cost_py(m, k, r, S):
    MT = meta.table(m, k, r)
    b1, b2 = meta.far(MT, S, 9)
    return len(b1) + len(b2)
checks = [(101, 25, 5), (127, 18, 24), (97, 24, 4), (137, 17, 16), (127, 21, 25)]
import json
for p, k, r in checks:
    kk = f'{p}_{k}_{r}'
    files = sorted(glob.glob(f'g/{kk}_L*.hits'))
    best = None
    for fn in files:
        for line in open(fn):
            c, x, y, z = map(int, line.split())
            if best is None or c < best[0]:
                best = (c, x, y, z)
    if best is None:
        print(kk, 'no hit lines'); continue
    c, x, y, z = best
    cp = cost_py(p, k, r, [0, x, y, z])
    print(f'{kk}: hx cost {c} with S={{0,{x},{y},{z}}}; independent numpy cost {cp}; {"AGREE" if cp == c else "DISAGREE"}')
