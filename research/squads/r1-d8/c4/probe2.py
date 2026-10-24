import sys, collections
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c4')
from c4lib import Torus
T = Torus(5)
def name(S):
    return tuple(sorted(S))
pc = collections.Counter(); lc = collections.Counter()
for O in T.pO: pc[(len(O), name(T.pstab[O[0]]))] += 1
for O in T.lO: lc[(len(O), name(T.lstab[O[0]]))] += 1
print('point orbits by (size, stab elements):')
for k_ in sorted(pc): print('  ', k_[0], pc[k_], k_[1] if len(k_[1])<=4 else ('|S|=%d' % len(k_[1])))
print('line orbits by (size, stab):')
for k_ in sorted(lc): print('  ', k_[0], lc[k_], k_[1] if len(k_[1])<=4 else ('|S|=%d' % len(k_[1])))
print('T list index->(a0,a1,a2):', [(d[0],d[1],d[2]) for d in T.T])
