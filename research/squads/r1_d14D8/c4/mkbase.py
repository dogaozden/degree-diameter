"""mkbase.py PARAMS OUT [m]: B-level base graph (for lifteval) from a symsa parameter file (lines 'k t w', 14 per point orbit).
Point global id PT[a][i] = g^a R_i, line LT[b][k] = g^b R_k; slot (i, s) gives edges (PT[a][i], LT[(a+t) % 133][k], w)."""
import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import write_base
params, out = sys.argv[1], sys.argv[2]
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 1
npz = np.load(f'/home/user/degree-diameter/research/squads/r1_d14D8/c4/sym_{seed}.npz')
PT, LT = npz['PT'], npz['LT']
S, NP = PT.shape
N = S * NP
P = np.loadtxt(params, dtype=np.int64).reshape(NP, 14, 3)
m = int(P[:, :, 2].max()) + 1
mm = int(sys.argv[4]) if len(sys.argv) > 4 else m
a = np.arange(S)
E = []
for i in range(NP):
    for s in range(14):
        k, t, w = P[i, s]
        E.append(np.stack([PT[a, i], LT[(a + t) % S, k], np.full(S, w)], axis=1))
E = np.concatenate(E)
write_base(out, N, mm, E)
print('wrote', out, 'edges', len(E), 'N', N, 'm', mm)
