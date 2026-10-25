import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/bcd-d8-r1/c6')
import base2 as b
Ms = [int(x) for x in sys.argv[1].split(',')]
seeds = range(int(sys.argv[2]), int(sys.argv[3]))
for M in Ms:
    res = []
    for s in seeds:
        rng = np.random.default_rng(1000 * s + M)
        pi = b.equiv_perm(b.H.porb, b.H.ppos, b.H.prep, rng, b.TP)
        rho = b.equiv_perm(b.H.lorb, b.H.lpos, b.H.lrep, rng, b.TL)
        E, inv, nk = b.build_edges(pi, rho)
        w = rng.integers(0, M, nk)
        p = f'{b.HERE}/rnd_{M}_{s}.spec'
        b.write_spec(p, M, E, inv, w)
        t = time.time(); c = b.cost(p); res.append(c)
        print(f'M={M} seed={s} cost={c} t={time.time()-t:.2f}', flush=True)
    print('M', M, 'costs', res, flush=True)
