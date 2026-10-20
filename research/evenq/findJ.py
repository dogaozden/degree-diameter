"""Find linear maps J of Pi_z (coords x0,x1,x2,x4,x5,x6; X3 eliminated) with Jx on the S_z-line of x for all x.
EVENQ_DELTA=d python3 findJ.py q a b"""
import sys
import numpy as np
from frame import Frame
q, a, b = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
Fr = Frame(q); H = Fr.H; F = H.F; ADD, MUL, INV = F.ADD, F.MUL, F.INV; d = Fr.delta
C = [0, 1, 2, 4, 5, 6]
Sz = Fr.Sz(a, b)
def nullspace(M):
    M = M.copy(); piv, r = [], 0
    for c in range(M.shape[1]):
        nz = np.nonzero(M[r:, c])[0]
        if len(nz) == 0: continue
        i = r + nz[0]; M[[r, i]] = M[[i, r]]; M[r] = MUL[M[r], INV[M[r, c]]]
        f = M[:, c].copy(); f[r] = 0; rr = np.nonzero(f)[0]
        if len(rr): M[rr] = ADD[M[rr], MUL[f[rr][:, None], M[r][None, :]]]
        piv.append(c); r += 1
        if r == M.shape[0]: break
    out = []
    for fc in [c for c in range(M.shape[1]) if c not in piv]:
        y = np.zeros(M.shape[1], np.int64); y[fc] = 1
        for i, pc in enumerate(piv): y[pc] = M[i, fc]
        out.append(y)
    return out
rows = []
for s in Sz[:60]:
    pts = H.P[H.lines[s]][:, C]
    # functionals vanishing on the line: nullspace of the 2 x 6 matrix of two points
    fs = nullspace(pts[:2].copy())
    for x in pts[:3]:
        for f in fs:
            # f(Jx) = sum_{i,j} f_i J_ij x_j : coefficient of J_ij is f_i x_j
            rows.append(MUL[f[:, None], x[None, :]].ravel())
sol = nullspace(np.array(rows))
print('q', q, 'delta', d, 'z', (a, b), 'dim of J-space', len(sol))
for y in sol:
    J = y.reshape(6, 6)
    print(J.tolist())
np.save(f'runs/J_q{q}_d{d}_z{a}_{b}.npy', np.array(sol))
