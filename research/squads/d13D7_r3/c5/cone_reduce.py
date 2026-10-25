# c5: reduced problem on the structured family "lines in direction u + one lift per cone class" (at infinity).
# Cone = points of H(11) with x0 = 0 and x5 = 2*x1 (mod 11) (1343 points incl. e4); its 122 classes are the lines through e4.
# usage: python3 -I cone_reduce.py OFFSETS [IDX_OUT]   (OFFSETS: "a b c e f" per line; lines are t + F*u, u = (1,0,0,9,0))
import struct, sys
import numpy as np
path = '/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin'
raw = open(path, 'rb').read()
q, N, L = struct.unpack('<iii', raw[:12])
co = np.frombuffer(raw[12 + 4 * L * (q + 1):], dtype=np.uint8).reshape(N, 7).astype(np.int64)
p = 11
u = np.array([1, 0, 0, 9, 0])
def Bmat(X, Y):
    # B(x,y) = x0 y4 + x4 y0 + x1 y5 + x5 y1 + x2 y6 + x6 y2 - 2 x3 y3 (mod 11), rows of X vs rows of Y
    return (np.outer(X[:, 0], Y[:, 4]) + np.outer(X[:, 4], Y[:, 0]) + np.outer(X[:, 1], Y[:, 5]) + np.outer(X[:, 5], Y[:, 1])
            + np.outer(X[:, 2], Y[:, 6]) + np.outer(X[:, 6], Y[:, 2]) - 2 * np.outer(X[:, 3], Y[:, 3])) % p
cone = np.where((co[:, 0] == 0) & ((co[:, 5] - 2 * co[:, 1]) % p == 0))[0]
e4 = [i for i in cone if co[i, 4] == 1 and not co[i, [1, 2, 3, 5, 6]].any()]
assert len(e4) == 1 and len(cone) == 1343, (len(cone), e4)
e4 = e4[0]
# classes: projection (x1,x2,x3,x5,x6) normalised to first nonzero = 1
def proj_key(x):
    v = [int(x[1]), int(x[2]), int(x[3]), int(x[5]), int(x[6])]
    nz = [t for t in v if t % p]
    if not nz: return None
    inv = pow(nz[0], p - 2, p)
    return tuple(int((t * inv) % p) for t in v)
classes = {}
for i in cone:
    if i == e4: continue
    classes.setdefault(proj_key(co[i]), []).append(i)
print('cone classes', len(classes), 'lifts per class', set(len(v) for v in classes.values()))
def affine_points(offsets):
    pts = []
    for (a, b, c, e, f) in offsets:
        for lam in range(p):
            a2, b2, c2, e2, f2 = (a + lam * 1) % p, b % p, c % p, (e + lam * 9) % p, f % p
            pts.append([1, a2, b2, c2, (c2 * c2 - a2 * e2 - b2 * f2) % p, e2, f2])
    return np.array(pts, dtype=np.int64)
def reduce_count(offsets):
    A = affine_points(offsets)
    usable = []
    for key, lifts in classes.items():
        Z = co[lifts]
        ok = (Bmat(A, Z) != 0).all(axis=0)     # lift compatible with all affine points of the lines
        if ok.any(): usable.append((key, [lifts[j] for j in np.where(ok)[0]]))
    return usable
if __name__ == '__main__':
    offs = [tuple(int(t) for t in l.split()) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
    usable = reduce_count(offs)
    print('lines', len(offs), 'usable cone classes m =', len(usable), ' total =', 11 * len(offs) + len(usable))
    if len(sys.argv) > 2:
        # choose the first compatible lift per usable class and write point indices (lines + lifts + e4 not used)
        A_idx = []
        for (a, b, c, e, f) in offs:
            for lam in range(p):
                a2, b2, c2, e2, f2 = (a + lam) % p, b % p, c % p, (e + 9 * lam) % p, f % p
                x = np.array([1, a2, b2, c2, (c2 * c2 - a2 * e2 - b2 * f2) % p, e2, f2])
                A_idx.append(x)
        chosen = [lifts[0] for (_, lifts) in usable]
        code = co @ (p ** np.arange(7))
        ids = []
        for x in A_idx:
            ids.append(int(np.searchsorted(code, int(x @ (p ** np.arange(7))))))
        out = sorted(set(ids) | set(int(c) for c in chosen))
        with open(sys.argv[2], 'w') as fh:
            fh.write(f'# reduced set: {len(offs)} lines + {len(usable)} cone lifts = {len(out)} points\n')
            fh.write('\n'.join(str(i) for i in out) + '\n')
        print('wrote', len(out), 'points to', sys.argv[2])
