#!/usr/bin/env python3
"""(k-variant: group file may be Q x Z_k, header p,-L0,k.) Independent BFS for large G = F_p^2 x| Q (cay_mg group file), N up to ~2^40, low memory (N bytes shared).
usage: indep_dist.py FILE d K lev vr vc ... [lev vr vc (involution)]   env NPROC (default: all cores)
One uint8 distance array (dist = layer+1, 0 = unseen) in shared anonymous memory; each layer the workers scan disjoint
ranges for the current layer and write layer+1 to unseen neighbours (concurrent writes store the same value).
Level maps and rho(x)^-1 come from explicit python matrix products; (u,v)(x,y) = (u x, rho(x)^-1 v + y)."""
import sys, os, struct, mmap
import numpy as np
f = open(sys.argv[1], 'rb'); p, L0 = struct.unpack('ii', f.read(8))
if L0 < 0: L0 = -L0; ZK, = struct.unpack('i', f.read(4))
else: ZK = 1
assert ZK >= 1
Q0 = [struct.unpack('iiii', f.read(16)) for _ in range(L0)]
# levels of Q0 x Z_k: index j*L0+i <-> (Q0[i], j); Z_k acts trivially on F_p^2
L = L0 * ZK
d, K = int(sys.argv[2]), int(sys.argv[3]); rest = list(map(int, sys.argv[4:])); H = d // 2; INV = d & 1
if len(rest) != 3 * (H + INV): sys.exit("expected %d numbers after K, got %d" % (3 * (H + INV), len(rest)))
if K > 250: sys.exit("K too large for uint8 distances")
pos0 = {m: i for i, m in enumerate(Q0)}
if len(pos0) != L0: sys.exit("duplicate matrices in Q")
def mm0(X, Y): return ((X[0]*Y[0]+X[1]*Y[2]) % p, (X[0]*Y[1]+X[1]*Y[3]) % p, (X[2]*Y[0]+X[3]*Y[2]) % p, (X[2]*Y[1]+X[3]*Y[3]) % p)
def inv0(X):
    det = (X[0]*X[3]-X[1]*X[2]) % p; di = pow(det, -1, p)
    return ((X[3]*di) % p, (-X[1]*di) % p, (-X[2]*di) % p, (X[0]*di) % p)
Minv0 = [inv0(m) for m in Q0]
def lvinv(x): return ((ZK - x // L0) % ZK) * L0 + pos0[inv0(Q0[x % L0])]
S = []
for i in range(H + INV):
    lev, vr, vc = rest[3*i:3*i+3]; S.append((lev, vr, vc))
    if i < H:
        ui = lvinv(lev); M = Minv0[ui % L0]
        S.append((ui, (-(M[0]*vr + M[1]*vc)) % p, (-(M[2]*vr + M[3]*vc)) % p))
ng = len(S)
jblk = np.repeat(np.arange(ZK, dtype=np.int64), L0)
DL = np.empty((ng, L), dtype=np.int64); W0 = np.empty((ng, L), dtype=np.int64); W1 = np.empty((ng, L), dtype=np.int64)
Mi = np.array(Minv0, dtype=np.int64)
for g, (u, vr, vc) in enumerate(S):
    Qu = Q0[u % L0]; base = np.array([pos0[mm0(Qu, Q0[i])] for i in range(L0)], dtype=np.int64)
    DL[g] = ((u // L0 + jblk) % ZK) * L0 + np.tile(base, ZK)
    W0[g] = np.tile((Mi[:, 0] * vr + Mi[:, 1] * vc) % p, ZK); W1[g] = np.tile((Mi[:, 2] * vr + Mi[:, 3] * vc) % p, ZK)
P2 = p * p; N = L * P2
buf = mmap.mmap(-1, N); dist = np.frombuffer(buf, dtype=np.uint8); dist[0] = 1
NP = int(os.environ.get('NPROC') or os.cpu_count()); SCAN = 1 << 26; CH = 1 << 22

def expand(lo, hi, cur):
    nxt = np.uint8(cur + 1)
    for a in range(lo, hi, SCAN):
        b = min(a + SCAN, hi); idx = np.flatnonzero(dist[a:b] == cur)
        for s in range(0, len(idx), CH):
            c = idx[s:s+CH].astype(np.int64) + a; x = c // P2; y1 = (c // p) % p; y2 = c % p
            for g in range(ng):
                ids = (DL[g][x] * p + (W0[g][x] + y1) % p) * p + (W1[g][x] + y2) % p
                ids = ids[dist[ids] == 0]; dist[ids] = nxt

def count(v):
    return sum(int(np.count_nonzero(dist[a:min(a + SCAN, N)] == v)) for a in range(0, N, SCAN))

bounds = [N * i // NP for i in range(NP + 1)]
sizes = [1]; total = 1
for t in range(1, K + 1):
    pids = []
    for i in range(NP):
        pid = os.fork()
        if pid == 0:
            expand(bounds[i], bounds[i + 1], t); os._exit(0)
        pids.append(pid)
    for pid in pids:
        _, st = os.waitpid(pid, 0)
        if st != 0: sys.exit("worker failed status %d at layer %d" % (st, t))
    n = count(t + 1); sizes.append(n); total += n
    print("layer", t, n, flush=True)
    if n == 0: break
print("order", N, "reached", total, "defect", N - total, "layers", sizes)
