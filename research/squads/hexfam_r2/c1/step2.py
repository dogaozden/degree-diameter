import sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/hexfam_r2/c1')
from lib import *
t = time.time()
allp = list(PERMS.values())
lab = orbit_labels(allp)
K, sizes, bad, conf = orbit_report(lab)
print('G2(3) orbits', K, 'time', round(time.time()-t,2))
import collections
print('sizes', sorted(collections.Counter(sizes.tolist()).items()))
print('bad', bad.sum(), 'good sizes', sorted(sizes[~bad].tolist()))
# 4306 set distribution
S = [int(x) for x in open('/home/user/degree-diameter/research/projects/hexagon-family/sets/P9_ncol_4306.txt').read().split()]
print('record ncol', is_ncol(S), len(S))
print('record orbit distribution', collections.Counter(lab[S].tolist()).most_common(10))
