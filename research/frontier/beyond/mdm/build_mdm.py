#!/usr/bin/env python3
"""Multi-doubled-matching lift of the generalized quadrangle W(q) (job new-cells-beyond, 2026-10-26).

Base: W(q) incidence graph (points 0..N-1, lines N..2N-1, read from gqgen's gq/gq_q{q}.bin), a parity nu(flag) in Z2
and k bijections sigma_1..sigma_k: points -> lines.  Voltage group Z2 x Z_M, M = 2k+1.  Lift vertices (v, a, b),
a in Z2, b in Z_M; edges (point -> line direction):
  flag (p, l):                     (p, a, b) ~ (l, a + nu(p,l), b)
  doubled matching i = 1..k, c=0,1: (p, a, b) ~ (sigma_i(p), a + c, b + i)
Degree q + 1 + 2k, 2M * 2N = 4(2k+1)(q+1)(q^2+1) vertices, bipartite.  Claim (DM_D5.md for k = 1, same proof for
every k, since {0, +-1, ..., +-k} = Z_M): diameter <= 5 whenever, for every pair of opposite points and every pair of
opposite lines, the q+1 geodesics do not all have the same nu-parity (condition (A); sigma_i arbitrary).
nu and sigma_1 come from a dmfast OUT file (lift2 DM format; dmfast with NOROUTE=1 anneals exactly condition (A));
sigma_2..sigma_k are random bijections (seed).
usage: build_mdm.py GQBIN DMFILE k seed OUT.edges"""
import sys, struct, random

def main():
    gqbin, dmf, k, seed, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    raw = open(gqbin, 'rb').read()
    q, N, L = struct.unpack('<3i', raw[:12])
    Q1 = q + 1
    pl = struct.unpack('<%di' % (L * Q1), raw[12:12 + 4 * L * Q1])
    tok = open(dmf).read().split()
    qq, jj = int(tok[0]), int(tok[1]); assert qq == q
    pos = 5 + 2  # header 5 numbers, then "cyc 6"
    sig1 = [int(x) for x in tok[pos:pos + N]]; pos += N * jj      # jj copies of sigma (identical)
    pos += N * jj                                                  # matching voltages (1 and 4)
    nu = [(int(x) // 3) & 1 for x in tok[pos:pos + L * Q1]]
    assert len(nu) == L * Q1 and sorted(sig1) == list(range(N))
    rng = random.Random(seed)
    sigs = [sig1]
    for i in range(1, k):
        s = list(range(N)); rng.shuffle(s); sigs.append(s)
    M = 2 * k + 1
    def vid(v, a, b): return (v * 2 + a) * M + b
    n = 2 * N * 2 * M
    with open(out, 'w') as f:
        f.write(f"{n}\n")
        for l in range(L):
            for kk in range(Q1):
                p = pl[l * Q1 + kk]; nv = nu[l * Q1 + kk]
                for a in range(2):
                    for b in range(M):
                        f.write(f"{vid(p, a, b)} {vid(N + l, a ^ nv, b)}\n")
        for i, s in enumerate(sigs, 1):
            for p in range(N):
                for a in range(2):
                    for b in range(M):
                        for c in range(2):
                            f.write(f"{vid(p, a, b)} {vid(N + s[p], a ^ c, (b + i) % M)}\n")
    print(f"q={q} k={k} M={M} vertices={n} degree={q + 1 + 2 * k}")

main()
