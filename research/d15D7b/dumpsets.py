#!/usr/bin/env python3
"""dumpsets.py: write the freed sets of master's typed (15,7) solution (R_H points, R_L lines; orbits of the order-133
collineation expanded) and the mirrored set R' with sigma, as plain id lists for the C tools.
usage: dumpsets.py HEXBIN TYPED_SOL MIRROR_SOL OUTDIR   (writes RH.txt, RL.txt, Rp.txt, sigma.txt)"""
import sys, numpy as np
hexfn, solfn, mirfn, od = sys.argv[1:5]
b = open(hexfn, 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
X = np.frombuffer(b[12 + 4 * Lc * Q1:], dtype=np.uint8).reshape(N, 7).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
order = np.lexsort((flat_l, flat_p)); PL = flat_l[order].reshape(N, Q1)
tok = open(solfn).read().split(); ti = 0
def nxt():
    global ti
    ti += 1; return tok[ti - 1]
assert nxt() == 'typed5s'
qq, NN, L, T, m, n0 = int(nxt()), int(nxt()), int(nxt()), nxt(), int(nxt()), int(nxt())
assert nxt() == 'gmat'
g = np.array([int(nxt()) for _ in range(9)], dtype=np.int64).reshape(3, 3)
det = int(round(np.linalg.det(g))) % q
adjg = np.array([[((g[(j + 1) % 3][(i + 1) % 3] * g[(j + 2) % 3][(i + 2) % 3]
                    - g[(j + 1) % 3][(i + 2) % 3] * g[(j + 2) % 3][(i + 1) % 3])) % q for j in range(3)]
                 for i in range(3)], dtype=np.int64)
gi = (adjg * pow(det, q - 2, q)) % q
code = X @ (q ** np.arange(7, dtype=np.int64))
Y = np.zeros_like(X)
Y[:, 0:3] = (X[:, 0:3] @ g.T) % q; Y[:, 3] = X[:, 3]; Y[:, 4:7] = (X[:, 4:7] @ gi) % q
lead = np.argmax(Y != 0, axis=1)
inv = np.array([0] + [pow(a, q - 2, q) for a in range(1, q)], dtype=np.int64)
Y = (Y * inv[Y[np.arange(N), lead]][:, None]) % q
pp = np.searchsorted(code, Y @ (q ** np.arange(7, dtype=np.int64)))
a0, b0 = pp[LP[:, 0]], pp[LP[:, 1]]
hit = (PL[a0][:, :, None] == PL[b0][:, None, :]).reshape(Lc, -1)
perm = [pp, PL[a0, hit.argmax(axis=1) // Q1]]
np.savetxt(od + '/gperm_pts.txt', perm[0], fmt='%d'); np.savetxt(od + '/gperm_lines.txt', perm[1], fmt='%d')
for kd, name in ((0, 'RH'), (1, 'RL')):
    assert nxt() == name
    k = int(nxt()); reps = np.array([int(nxt()) for _ in range(k)], dtype=np.int64)
    s = np.zeros(N, bool); cur = reps.copy()
    for _ in range(m):
        s[cur] = True; cur = perm[kd][cur]
    np.savetxt(f'{od}/{name}.txt', np.nonzero(s)[0], fmt='%d')
    print(name, s.sum())
mt = open(mirfn).read().split('\n')
Rp = np.array([int(v) for v in mt[1].split()[1:]], dtype=np.int64)
sig = np.array([int(v) for line in mt[3:] for v in line.split()], dtype=np.int64)
np.savetxt(od + '/Rp.txt', Rp, fmt='%d'); np.savetxt(od + '/sigma.txt', sig, fmt='%d')
print("R'", len(Rp), 'sigma', len(sig))
