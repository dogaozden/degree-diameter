import random, time, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1-d8/c6')
from c6lib import *
q = int(sys.argv[1])
t0 = time.time()
H = load(q); N = H.N
print('loaded', N, time.time() - t0, flush=True)
X = collinear_lists(H)
print('closed nbhd size', set(len(x) for x in X), 'lines per pt', set(len(H.through[p]) for p in range(N)), flush=True)
