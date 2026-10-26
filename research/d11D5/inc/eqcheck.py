"""GF(2) consistency of the forced parity equations of a DM base: every same-side pair at pure distance 4 with exactly
two geodesics and no sigma-route (R) needs the two geodesics to have different nu-parity, i.e. the XOR of their flags
= 1.  Prints the number of such equations and whether they are consistent (Gaussian elimination over GF(2)).
(Opposite pairs at pure distance 5 are ignored here.)  usage: python3 eqcheck.py in.txt"""
import sys, numpy as np
f = open(sys.argv[1]).read().split()
n, dg = int(f[0]), int(f[1])
ln = np.array(f[2:2 + n * dg], dtype=int).reshape(n, dg); sig = np.array(f[2 + n * dg:2 + n * dg + n], dtype=int)
fid = {}
for l in range(n):
    for k in range(dg): fid[(int(ln[l, k]), l)] = l * dg + k
I = np.zeros((n, n), dtype=np.int64)
for l in range(n): I[ln[l], l] = 1
PP = I @ I.T; LL = I.T @ I; P4 = PP @ PP; L4 = LL @ LL
sinv = np.argsort(sig)
lines_of = [np.nonzero(I[p])[0].tolist() for p in range(n)]; pts_of = [ln[l].tolist() for l in range(n)]
eqs = []
# points: x - l1 - w - l2 - y
Rp = LL[np.ix_(sig, sig)] > 0
for x in range(n):
    for y in range(x + 1, n):
        if PP[x, y] == 0 and P4[x, y] == 2 and not Rp[x, y]:
            geos = []
            for l1 in lines_of[x]:
                for w in pts_of[l1]:
                    if w == x: continue
                    for l2 in lines_of[w]:
                        if l2 != l1 and I[y, l2]: geos.append((fid[(x, l1)], fid[(w, l1)], fid[(w, l2)], fid[(y, l2)]))
            assert len(geos) == 2, (x, y, geos)
            v = 0
            for g in geos:
                for fl in g: v ^= 1 << fl
            eqs.append(v)
Rl = PP[np.ix_(sinv, sinv)] > 0
for a in range(n):
    for b in range(a + 1, n):
        if LL[a, b] == 0 and L4[a, b] == 2 and not Rl[a, b]:
            geos = []
            for p1 in pts_of[a]:
                for m in lines_of[p1]:
                    if m == a: continue
                    for p2 in pts_of[m]:
                        if p2 != p1 and I[p2, b]: geos.append((fid[(p1, a)], fid[(p1, m)], fid[(p2, m)], fid[(p2, b)]))
            assert len(geos) == 2, (a, b, geos)
            v = 0
            for g in geos:
                for fl in g: v ^= 1 << fl
            eqs.append(v)
print("forced equations (two-geodesic pairs without a sigma route):", len(eqs))
# Gaussian elimination: equations v = 1 (rhs bit at position NF)
NF = n * dg; piv = {}
bad = 0
for v in eqs:
    r = v | (1 << NF)
    while True:
        low = r & ((1 << NF) - 1)
        if low == 0: break
        hb = low.bit_length() - 1
        if hb in piv: r ^= piv[hb]
        else: piv[hb] = r; break
    if r & ((1 << NF) - 1) == 0 and r >> NF & 1: bad += 1
print("rank", len(piv), "inconsistent equations", bad)
