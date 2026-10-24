import sys, random, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c4')
from c4lib import Torus
import numpy as np
t0 = time.time()
T = Torus(5)
print('torus ok', T.nT, 'point orbits', len(T.pO), 'line orbits', len(T.lO), 'time', round(time.time()-t0, 2))
print('point stab counts (size->#orbits)', T.stab_counts())
print('orbit size hist points', sorted(collections_c for collections_c in __import__('collections').Counter(len(O) for O in T.pO).items()))
print('orbit size hist lines', sorted(__import__('collections').Counter(len(O) for O in T.lO).items()))
rng = random.Random(1)
try:
    s = T.matching(rng)
    T.check_equivariant(s)
    print('matching ok')
except ValueError as e:
    print('ERR', e)
