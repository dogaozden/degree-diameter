# mkmain3.py (job d7-family): main graph (no hubs) of the typed three-level H D H construction: R_H freed at 0->1, R_L
# at 1->2, mirrored R' at 2->0. usage: mkmain3.py HEXBIN RH.txt RL.txt Rp.txt sigma.txt OUT.edges
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hd5_masks import load_hex
hexfn, rh, rl, rp, sg, out = sys.argv[1:7]
q, N, LP, PL = load_hex(hexfn)
RH = np.loadtxt(rh, dtype=np.int64); RL = np.loadtxt(rl, dtype=np.int64); Rp = np.loadtxt(rp, dtype=np.int64); sig = np.loadtxt(sg, dtype=np.int64)
V = lambda j, k, x: 2 * N * j + k * N + x
fp = LP.reshape(-1); fl = np.repeat(np.arange(N), q + 1)
E = [np.stack([V(j, 0, fp), V(j, 1, fl)], 1) for j in range(3)]
x = np.arange(N)
k = np.ones(N, bool); k[RH] = False; E.append(np.stack([V(0, 0, x[k]), V(1, 0, x[k])], 1))      # 0->1 points
k = np.ones(N, bool); k[RL] = False; E.append(np.stack([V(1, 1, x[k]), V(2, 1, x[k])], 1))      # 1->2 lines
k = np.ones(N, bool); k[Rp] = False; E.append(np.stack([V(2, 0, x[k]), V(0, 1, sig[x[k]])], 1))  # 2->0 sigma
E = np.concatenate(E)
with open(out, 'w') as f:
    f.write(f'{6 * N}\n'); f.write('\n'.join(f'{a} {b}' for a, b in E.tolist())); f.write('\n')
print(len(E), 'edges')
