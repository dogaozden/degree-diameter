import numpy as np, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r4/c5')
from ovoid_field import *
def B(z_code, w_code, Lc):
    s = fadd(np.array([z_code]), np.array([w_code]))[0]
    return (Qcodes(np.array([s]), Lc)[0] - Qcodes(np.array([z_code]), Lc)[0] - Qcodes(np.array([w_code]), Lc)[0]) % 7
results = []
for Lc in [0, 1, 2, 3]:
    Qv_all = Qvals_logs(np.arange(M), Lc)
    singular_fibers = []
    for k in range(57):
        Ls = np.arange(k, 19608, 57)          # projective representatives with L = k mod 57
        vals = Qvals_logs(Ls, Lc)
        if (vals == 0).all():
            singular_fibers.append(k)
        else:
            assert not (vals == 0).any(), 'fiber not constant'
    print('Lc', Lc, 'singular fibers', singular_fibers)
    for k in singular_fibers:
        Ls = np.arange(k, 19608, 57)
        z0 = exp[Ls[0]]
        zs = exp[Ls]
        sums = fadd(np.full(zs.shape, z0), zs)
        Qs = Qcodes(sums, Lc)
        Qz0 = Qcodes(np.array([z0]), Lc)[0]
        Qzs = Qcodes(zs, Lc)
        Bv = (Qs - Qz0 - Qzs) % 7
        bad = int((Bv[1:] == 0).sum())
        print('  fiber', k, 'size', len(Ls), 'pairs with B=0 from z0:', bad)
        results.append((Lc, k, bad))
print(results)
