import sys, numpy as np, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d8c/c7')
from lift import *
q, k = int(sys.argv[1]), int(sys.argv[2])
N, LP, sig = make_base(q, 1)
rng = np.random.default_rng(5)
path = f'/home/user/degree-diameter/research/squads/r1_d8c/c7/runs/t_q{q}_k{k}.txt'
for name, hb, mb in [('zero', np.zeros(N*(q+1), int), np.zeros((2,N), int)),
                     ('rand', rng.integers(0, k, N*(q+1)), rng.integers(0, k, (2,N)))]:
    t = time.time(); n = write_lift(q, k, hb, mb, sig, path)
    t1 = time.time(); c = run_gcheck(path, 2*N)
    print(name, 'n', n, 'cost', c, 'write %.2fs check %.2fs' % (t1-t, time.time()-t1), flush=True)
