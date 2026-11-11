import numpy as np, sys, glob, pickle
sys.path.insert(0,'.')
from h66 import PERMS, H
PL = np.stack([PERMS[k] for k in sorted(PERMS)])  # 66 x H local perms
def canon(loc_set):
    """loc_set: array of local indices (one side). returns canonical key (min over H of sorted images) and all images"""
    imgs = PL[:, loc_set]               # 66 x k
    imgs.sort(axis=1)
    rows = [tuple(r) for r in imgs]
    return min(rows), set(rows)
def load_side_lines(path):
    out = []
    for line in open(path):
        ids = [int(x) for x in line.split()]
        if ids: out.append(ids)
    return out
if __name__ == '__main__':
    # 1) d06 solution: is it H-invariant? (side by id range)
    sol = load_side_lines('/home/user/degree-diameter/research/squads/beyond-small/r3/orbAB_27_21.txt')
    keysum = {}
    for ids in sol:
        side = 'B' if ids[0] >= H else 'A'
        loc = np.array([x - (H if x >= H else 0) for x in ids])
        key, rows = canon(loc)
        keysum.setdefault(side, {}).setdefault(key, 0)
        keysum[side][key] += 1
    for s in keysum:
        print('solution side', s, 'Z22 orbits', sum(keysum[s].values()), 'distinct H-orbits', len(keysum[s]),
              'sizes', sorted(keysum[s].values()))
