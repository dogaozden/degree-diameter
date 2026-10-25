#!/usr/bin/env python3
# prep.py E TAG: orbit conflict graph of POINTS of H(11) under h = g^E, g = order-133 collineation (shared/g133_pts.txt).
# E=19 gives h of order 7 (orbits of 7 points); E=7 gives h of order 19 (orbits of 19 points).
# Output (in c2/): graph_TAG.bin = int32 n, m, osz; n*osz int32 point ids (orbit v); m int32 pairs (a,b) of valid-orbit ids.
#                  init_TAG.txt = valid-orbit ids covering RH.txt.
import numpy as np, sys, math
D = '/home/user/degree-diameter/research/squads/c157b-r1/'
E = int(sys.argv[1]); TAG = sys.argv[2]
b = open(D + 'shared/hex_q11.bin', 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
g = np.loadtxt(D + 'shared/g133_pts.txt', dtype=np.int64).reshape(-1)
assert len(g) == N and len(np.unique(g)) == N
def perm_pow(p, k):
    res = np.arange(len(p), dtype=np.int64); base = p.copy()
    while k:
        if k & 1: res = base[res]
        base = base[base]; k >>= 1
    return res
h = perm_pow(g, E)
hl = h.tolist()
osz = 133 // math.gcd(E, 133)
orb = [-1] * N; orbits = []
for i in range(N):
    if orb[i] < 0:
        c = len(orbits); cyc = [i]; orb[i] = c; j = hl[i]
        while j != i:
            orb[j] = c; cyc.append(j); j = hl[j]
        orbits.append(cyc)
assert set(len(c) for c in orbits) == {osz}
NO = len(orbits)
orbit_pts = np.array(orbits, dtype=np.int64)
PO = np.array(orb, dtype=np.int64)
OP = PO[LP]                                  # orbit id of each point on each line (Lc x 12)
s = np.sort(OP, axis=1)
eq = s[:, 1:] == s[:, :-1]
bad = np.unique(s[:, 1:][eq])                # orbits with two points on one line (internally collinear)
valid = np.ones(NO, bool); valid[bad] = False
print('orbits', NO, 'osz', osz, 'internally collinear', len(bad), 'valid', int(valid.sum()))
keys = []
for a in range(Q1):
    x = OP[:, a]
    for c in range(a + 1, Q1):
        y = OP[:, c]
        msk = x != y
        keys.append(np.minimum(x, y)[msk] * NO + np.maximum(x, y)[msk])
keys = np.unique(np.concatenate(keys))
u = keys // NO; v = keys % NO
ok = valid[u] & valid[v]
u = u[ok]; v = v[ok]
vid = np.flatnonzero(valid)
newid = -np.ones(NO, np.int64); newid[vid] = np.arange(len(vid))
U = newid[u]; V = newid[v]
n = len(vid); m = len(U)
print('graph n', n, 'm', m, 'avg deg', 2 * m / n)
rh = np.loadtxt(D + 'shared/RH.txt', dtype=np.int64).reshape(-1)
ro = PO[rh]
cnt = np.bincount(ro, minlength=NO)
full = np.flatnonzero(cnt)
assert (cnt[full] == osz).all(), 'RH is not a union of orbits'
assert valid[full].all(), 'RH contains internally collinear orbit'
init = newid[full]
print('RH orbits', len(full), 'points', len(full) * osz)
with open(D + 'c2/graph_%s.bin' % TAG, 'wb') as f:
    f.write(np.array([n, m, osz], dtype=np.int32).tobytes())
    f.write(orbit_pts[vid].astype(np.int32).tobytes())
    f.write(np.stack([U, V], axis=1).astype(np.int32).tobytes())
np.savetxt(D + 'c2/init_%s.txt' % TAG, init, fmt='%d')
print('wrote graph_%s.bin init_%s.txt' % (TAG, TAG))
