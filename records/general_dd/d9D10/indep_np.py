#!/usr/bin/env python3
"""numpy independent BFS for large G = F_p^2 x| Q (cay_mg group file); chunked, int32 frontiers, uint8 visited.
usage: indep_np.py FILE d K lev vr vc ... [lev vr vc (involution)]
The per-generator level maps and the matrices rho(x)^-1 are computed in pure python from explicit matrix products;
only the BFS bookkeeping is vectorised. (u,v)(x,y) = (u x, rho(x)^-1 v + y)."""
import sys, struct
import numpy as np
f = open(sys.argv[1], 'rb'); p, L = struct.unpack('ii', f.read(8))
Q = [struct.unpack('iiii', f.read(16)) for _ in range(L)]
d, K = int(sys.argv[2]), int(sys.argv[3]); rest = list(map(int, sys.argv[4:])); H = d // 2; INV = d & 1
pos = {m: i for i, m in enumerate(Q)}
def mm(X, Y): return ((X[0]*Y[0]+X[1]*Y[2]) % p, (X[0]*Y[1]+X[1]*Y[3]) % p, (X[2]*Y[0]+X[3]*Y[2]) % p, (X[2]*Y[1]+X[3]*Y[3]) % p)
def inv(X):
    det = (X[0]*X[3]-X[1]*X[2]) % p; di = pow(det, -1, p)
    return ((X[3]*di) % p, (-X[1]*di) % p, (-X[2]*di) % p, (X[0]*di) % p)
Minv = [inv(m) for m in Q]
S = []
for i in range(H + INV):
    lev, vr, vc = rest[3*i:3*i+3]; S.append((lev, vr, vc))
    if i < H:
        ui = pos[inv(Q[lev])]; M = Minv[ui]
        S.append((ui, (-(M[0]*vr + M[1]*vc)) % p, (-(M[2]*vr + M[3]*vc)) % p))
ng = len(S)
DL = np.array([[pos[mm(Q[u], Q[x])] for x in range(L)] for (u, _, _) in S], dtype=np.int64)
Mi = np.array(Minv, dtype=np.int64)            # L x 4
W0 = np.zeros((ng, L), dtype=np.int64); W1 = np.zeros((ng, L), dtype=np.int64)
for g, (u, vr, vc) in enumerate(S):
    for x in range(L):
        M = Minv[x]; W0[g, x] = (M[0]*vr + M[1]*vc) % p; W1[g, x] = (M[2]*vr + M[3]*vc) % p
N = L * p * p
vis = np.zeros(N, dtype=np.uint8); vis[0] = 1
cur = np.zeros(1, dtype=np.int32); total = 1; sizes = [1]; CH = 1 << 22
for t in range(K):
    parts = []
    for a in range(0, len(cur), CH):
        c = cur[a:a+CH].astype(np.int64); x = c // (p*p); y1 = (c // p) % p; y2 = c % p
        for g in range(ng):
            z1 = (W0[g][x] + y1) % p; z2 = (W1[g][x] + y2) % p
            ids = (DL[g][x] * p + z1) * p + z2
            new = ids[vis[ids] == 0]
            new = np.unique(new); vis[new] = 1; parts.append(new.astype(np.int32))
    cur = np.concatenate(parts) if parts else np.zeros(0, dtype=np.int32)
    sizes.append(len(cur)); total += len(cur)
    if len(cur) == 0: break
print("order", N, "reached", total, "defect", N - total, "layers", sizes)
