import sys, time, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c1')
from fastlib import *
t = time.time()
R = list(MATS.keys())
def group_lab(names, extra=()):
    return forb([PERMS[n] for n in names] + list(extra))
lab = group_lab(R)
print('check G2 orbits', len(set(lab.tolist())), round(time.time()-t,2))
# long-root SL3(3)
L = [n for n in R if n.startswith('long')]; S = [n for n in R if n.startswith('short')]
for name, names in [('long', L), ('short', S)]:
    lab = group_lab(names)
    K, sizes, bad, conf = summarize(lab)
    print(name, 'K', K, 'sizes', sorted(collections.Counter(sizes.tolist()).items())[:20], 'bad', bad.sum(), 'good sizes', sorted(sizes[~bad].tolist())[-10:], round(time.time()-t,2), flush=True)
