#!/usr/bin/env python3
"""Build the hub graph of a Lemma 4.2 certificate (hubsum.py) and write it as an edge list for `hgcheck edges`.
usage: build_cert.py q k HEXDIR OUT.txt [SEED] [--typed]
HEXDIR holds hex_q{s}.bin from research/d10D7/hexgen2.c for the hexagons H(s) the certificate uses.
Parts: blown-up H(s) (Lemma 4.1: each point and line gets 1..c copies, copies of incident elements adjacent), a plane
PG(2,p) with pendant trees (Lemma 4.3; p prime here), joined by random injections A_j -> B_i, B_j -> A_i (i < j)."""
import sys, random, struct
import numpy as np
from hubopt import optimise
from hubcap_lib import slots, PP

def read_hex(path):
    with open(path, 'rb') as f:
        q, N, L = struct.unpack('3i', f.read(12))
        lines = np.frombuffer(f.read(4 * L * (q + 1)), dtype=np.int32).reshape(L, q + 1)
    return N, lines

def blowup(s, c, x, y, hexdir, rng):
    N, lines = read_hex('%s/hex_q%d.bin' % (hexdir, s))
    tp = np.ones(N, int); tl = np.ones(N, int)
    for t, tot in ((tp, x), (tl, y)):
        extra = tot - N
        assert 0 <= extra <= (c - 1) * N
        idx = np.repeat(np.arange(N), c - 1); rng.shuffle(idx)
        np.add.at(t, idx[:extra], 1)
    po = np.concatenate([[0], np.cumsum(tp)]); lo = np.concatenate([[0], np.cumsum(tl)])
    E = []
    for l in range(N):
        for p in lines[l]:
            for a in range(po[p], po[p + 1]):
                for b in range(lo[l], lo[l + 1]):
                    E.append((a, b))
    return x, y, E

def plane(p):
    """incidence of PG(2,p), p prime: points and lines = normalised nonzero vectors"""
    pts = []
    for a in range(p):
        for b in range(p):
            pts.append((1, a, b))
    for b in range(p):
        pts.append((0, 1, b))
    pts.append((0, 0, 1))
    inc = [[i for i, x in enumerate(pts) if (x[0] * l[0] + x[1] * l[1] + x[2] * l[2]) % p == 0] for l in pts]
    return len(pts), inc

def tree(d, x, y, rng):
    for s in PP:
        if s + 1 > d: break
        if any(s % r == 0 for r in range(2, s)):     # prime s only (enough for the certificates used)
            continue
        n = s * s + s + 1
        if n > min(x, y): break
        t = d - s - 1; u = d - 1
        cP = min(t * n, y - n)
        lo_ = max(0, x - n - u * cP, -(-(y - n - cP) // u))
        hi = min(t * n, x - n)
        if lo_ <= hi:
            cL = lo_; gP = x - n - cL; gL = y - n - cP
            break
    else:
        raise SystemExit('no prime core')
    n, inc = plane(s)
    E = [(pt, l) for l in range(n) for pt in inc[l]]       # A = points, B = lines
    A = n; B = n
    # c_P children (colour B) under points, at most t each; c_L children (colour A) under lines
    pc = []
    for i in range(cP):
        par = i % n; E.append((par, B)); pc.append(B); B += 1
    lc = []
    for i in range(cL):
        par = i % n; lc.append(A); E.append((A, par)); A += 1
    for i in range(gP):                                     # grandchildren colour A under point-children (colour B)
        E.append((A, pc[i % len(pc)])); A += 1
    for i in range(gL):                                     # grandchildren colour B under line-children (colour A)
        E.append((lc[i % len(lc)], B)); B += 1
    assert A == x and B == y
    return x, y, E

def main():
    q, k, hexdir, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    rng = np.random.default_rng(int(sys.argv[5]) if len(sys.argv) > 5 and sys.argv[5].isdigit() else 1)
    KB, KA = slots(q, k)
    tot, K1, K2, sol = optimise(KB, KA, q - k)
    assert sol, 'no certificate'
    print('certificate:', sol)
    parts = []
    for p in sol:
        parts.append(blowup(p[1], p[2], p[3], p[4], hexdir, rng) if p[0] == 'core' else tree(p[1], p[2], p[3], rng))
    offA = np.cumsum([0] + [pt[0] for pt in parts]); offB = np.cumsum([0] + [pt[1] for pt in parts])
    E = []
    for i, (x, y, Ei) in enumerate(parts):
        E.extend((offA[i] + a, offB[i] + b) for (a, b) in Ei)
    r = len(parts)
    for j in range(r):
        for i in range(j):
            xj, yj, _ = parts[j]; xi, yi, _ = parts[i]
            assert xj <= yi and yj <= xi
            for a, b in zip(range(xj), rng.permutation(yi)[:xj]):      # A_j -> B_i
                E.append((offA[j] + a, offB[i] + b))
            for b, a in zip(range(yj), rng.permutation(xi)[:yj]):      # B_j -> A_i
                E.append((offA[i] + a, offB[j] + b))
    with open(out, 'w') as f:
        if '--typed' in sys.argv:                     # typed_build.py hub file: first line K (equal sides)
            assert offA[-1] == offB[-1]
            f.write('%d\n' % offA[-1])
        else:
            f.write('%d %d\n' % (offA[-1], offB[-1]))
        for a, b in E:
            f.write('%d %d\n' % (a, b))
    print('wrote', out, 'K1 =', offA[-1], 'K2 =', offB[-1], 'edges =', len(E))

if __name__ == '__main__':
    main()
