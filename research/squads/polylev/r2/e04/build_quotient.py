"""Orbit quotient of the collinearity graph of H(13) by the order-61 semiregular group S61_q13.pperm.

Exact at point level (no group-invariance assumption): an orbit is admissible iff none of its points is collinear
with another point of the same orbit; orbits O1, O2 (both admissible) are adjacent iff some point of O1 is collinear
with some point of O2. Output: CSR graph in the mis2 format (PREFIX_n.bin, PREFIX_off.bin, PREFIX_nb.bin) over the
admissible orbits, plus PREFIX_orb.bin (orbit id of each quotient vertex) and orb.bin (orbit id of each point).
"""
import struct, sys, numpy as np

HEX = '/home/user/degree-diameter/research/theorems/polylev/hex/hex_q13.bin'
GRP = '/home/user/degree-diameter/research/theorems/polylev/grp/S61_q13'
OUT = '/home/user/degree-diameter/research/squads/polylev/r2/e04/work'

with open(HEX, 'rb') as f:
    q, N, L = struct.unpack('3i', f.read(12))
    lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1).astype(np.int64)
assert (q, N, L) == (13, 402234, 402234), (q, N, L)
pperm = np.fromfile(GRP + '.pperm', dtype=np.int32).astype(np.int64)
lperm = np.fromfile(GRP + '.lperm', dtype=np.int32).astype(np.int64)
assert len(pperm) == N and len(lperm) == L

# the permutations must be collineations: pperm maps line l onto line lperm[l]
img = np.sort(pperm[lines], axis=1)
tgt = np.sort(lines[lperm], axis=1)
assert (img == tgt).all(), 'pperm is not a collineation'
print('collineation check ok', flush=True)

# lines through each point (every point lies on q+1 lines)
flat = lines.ravel()
assert (np.bincount(flat, minlength=N) == q + 1).all()
order = np.argsort(flat, kind='stable')
PL = (order // (q + 1)).reshape(N, q + 1)

# orbits = cycles of pperm (all of length 61)
orb = -np.ones(N, dtype=np.int64)
R = 0
for s in range(N):
    if orb[s] >= 0:
        continue
    x = s
    while orb[x] < 0:
        orb[x] = R
        x = pperm[x]
    R += 1
sizes = np.bincount(orb, minlength=R)
assert (sizes == 61).all(), 'orbits not all of size 61'
print('orbits', R, flush=True)

# point-level pass: inadmissible orbits and directed orbit-conflict keys
bad = np.zeros(R, dtype=bool)
keys = []
CH = 20000
for c0 in range(0, N, CH):
    v = np.arange(c0, min(N, c0 + CH))
    nbm = lines[PL[v]]                                  # (k, q+1, q+1)
    nbm = nbm.reshape(len(v), (q + 1) * (q + 1))
    mask = nbm != v[:, None]                            # drop v itself (once per line)
    nb = nbm[mask].reshape(len(v), q * (q + 1))         # 182 collinear points per point
    assert nb.shape[1] == q * (q + 1)
    a = np.repeat(orb[v], nb.shape[1])
    b = orb[nb.ravel()]
    same = a == b
    if same.any():
        bad[np.unique(a[same])] = True
    k = np.unique(a[~same] * R + b[~same])
    keys.append(k)
keys = np.unique(np.concatenate(keys))
ka, kb = keys // R, keys % R
print('inadmissible orbits', int(bad.sum()), 'admissible', int(R - bad.sum()), 'directed conflict pairs', len(keys), flush=True)

adm = ~bad
newid = -np.ones(R, dtype=np.int64)
ids = np.nonzero(adm)[0]
newid[ids] = np.arange(len(ids))
ok = adm[ka] & adm[kb]
ka2, kb2 = newid[ka[ok]], newid[kb[ok]]
# symmetry check (exact collinearity is symmetric, so every pair must appear both ways)
kk = ka2 * len(ids) + kb2
rev = kb2 * len(ids) + ka2
print('asymmetric pairs', int((~np.isin(kk, rev)).sum()), flush=True)
o = np.lexsort((kb2, ka2))
ka2, kb2 = ka2[o], kb2[o]
n = len(ids)
deg = np.bincount(ka2, minlength=n)
off = np.zeros(n + 1, dtype=np.int64); off[1:] = np.cumsum(deg)
print('quotient n', n, 'edges(directed)', len(kb2), 'deg min/mean/max', deg.min(), deg.mean(), deg.max(), flush=True)

pref = OUT + '/Q'
np.array([n], dtype=np.int32).tofile(pref + '_n.bin')
off.astype(np.int32).tofile(pref + '_off.bin')
kb2.astype(np.int32).tofile(pref + '_nb.bin')
ids.astype(np.int32).tofile(pref + '_orb.bin')
orb.astype(np.int32).tofile(OUT + '/orb.bin')
print('written', pref, flush=True)
