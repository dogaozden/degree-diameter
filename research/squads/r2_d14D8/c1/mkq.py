"""mkq.py q k seed out: random initial level-family design, Sigma-symmetric quotient (c1, squad r2_d14D8).

Quotient: point orbits i (NP of them, size S = |Sigma|), slots e = D*i + s, D = q + 3.
  s < q+1 : hexagon flag from rep R_i to line g^T repL[K] (level 0), (K, T) from orbL/shL of the line.
  s = D-2, D-1 : phi-edges, same bijection phi (doubled), phi(g^a R_i) = g^(a+u_i) repL[pi(i)],
                 i.e. (K, T) = (pi(i), u_i) for both slots, levels 1 and 2.
Sub-voltages C in Z_k for every slot (random). Lift voltage = CRT(LEV mod 5, C mod k) in Z_{5k}.
File: header 'NP S D', then NP*D lines 'K T LEV C'."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d14D8_work')
from hexlib import load, HERE
q, k, seed = map(int, sys.argv[1:4]); out = sys.argv[4]
N, LP, PL, coord = load(q)
z = np.load(HERE / 'hex' / f'sym_q{q}.npz')
S = int(z['S']); repP = z['repP']; orbL = z['orbL']; shL = z['shL']
NP = len(repP); D = q + 3
rng = np.random.default_rng(seed)
pi = rng.permutation(NP); u = rng.integers(0, S, NP)
C = rng.integers(0, k, (NP, D))
with open(out, 'w') as f:
    f.write(f'{NP} {S} {D}\n')
    for i in range(NP):
        R = repP[i]
        for s in range(q + 1):
            L = PL[R][s]
            f.write(f'{orbL[L]} {shL[L]} 0 {C[i, s]}\n')
        for lev in (1, 2):
            f.write(f'{pi[i]} {u[i]} {lev} {C[i, D - 3 + lev]}\n')
print(f'wrote {out}: q={q} NP={NP} S={S} D={D} k={k}')
