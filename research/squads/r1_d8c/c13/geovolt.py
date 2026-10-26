"""c13: additive projective-parameter voltages with geometric base points (q prime).

Base graph: points 0..N-1, lines 0..N-1 of H(q), flags (p, L) with voltage t(p,L) in Z_q, where for each line L
 e_L = point of L nearest (incidence distance, ties by lex) to a fixed point a, f_L = point of L nearest to b
 (excluding e_L), p = <e_L + t f_L>, t in GF(q), and p = f_L gets t = inf -> value CINF.
Group: Z_{5q} = Z_5 x Z_q (q != 5). Hexagon flags get (0 mod 5, t mod q).
Matchings sigma_1, sigma_2: points -> lines bijection phi, voltages (1 mod 5, 0) and (2 mod 5, 0).
Usage: geovolt.py q MODE CINF OUTFILE   (MODE: 'idx' = phi by storage index shift avoiding incidences,
       'geo' = phi matches geometric keys order)
"""
import sys
import numpy as np
from collections import deque
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load, dist_from_point

q = int(sys.argv[1]); MODE = sys.argv[2]; CINF = int(sys.argv[3]); OUT = sys.argv[4]
J = int(sys.argv[5]) if len(sys.argv) > 5 else 5
N, LP, PL, coord = load(q)
C = coord.astype(np.int64) % q

def norm(v):
    v = v % q
    nz = np.nonzero(v)[0][0]
    inv = pow(int(v[nz]), q - 2, q)
    return tuple(int(x) for x in (v * inv) % q)

NV = [norm(C[p]) for p in range(N)]
# distances from a and b (points) ; a = point 0, b = a point at incidence distance 6 from a if possible
a = 0
dpa, _ = dist_from_point(a, LP, PL, maxd=6)
cand = np.nonzero(dpa == 6)[0]
b = int(cand[0]) if len(cand) else 1
dpb, _ = dist_from_point(b, LP, PL, maxd=6)

def lexkey(p):
    return NV[p]

eL = np.zeros(N, dtype=np.int64); fL = np.zeros(N, dtype=np.int64)
for L in range(N):
    pts = [int(x) for x in LP[L]]
    e = min(pts, key=lambda p: (int(dpa[p]), int(dpb[p]), lexkey(p)))
    rest = [p for p in pts if p != e]
    f = min(rest, key=lambda p: (int(dpb[p]), int(dpa[p]), lexkey(p)))
    eL[L] = e; fL[L] = f

# voltage of flag (p,L): t with p = <e + t f>, p == f -> CINF, p == e -> 0
volt = np.zeros((N, N), dtype=np.int64)  # volt[p, L]
for L in range(N):
    e, f = int(eL[L]), int(fL[L])
    ve = np.array(NV[e]); vf = np.array(NV[f])
    table = {}
    table[norm(ve)] = 0
    for t in range(q):
        table[norm((ve + t * vf) % q)] = t
    table[norm(vf)] = CINF % q
    for p in LP[L]:
        volt[int(p), L] = table[NV[int(p)]]

# incidence check
assert all(NV[p] is not None for p in range(N))

# CRT: Z_{5q} ~ Z_5 x Z_q
m = J * q
def crt(x5, xq):
    for x in range(m):
        if x % J == x5 % J and x % q == xq % q:
            return x
S1 = int(sys.argv[6]) if len(sys.argv) > 6 else 1
S2 = int(sys.argv[7]) if len(sys.argv) > 7 else 2
SH1 = int(sys.argv[8]) if len(sys.argv) > 8 else 0
SH2 = int(sys.argv[9]) if len(sys.argv) > 9 else 0
sig_volt = [crt(S1, 0), crt(S2, 0)]
assert len(set(sig_volt)) == 2 and 0 not in sig_volt

# matchings phi: points -> lines bijection
inc = set()
for L in range(N):
    for p in LP[L]:
        inc.add((int(p), L))
if MODE == 'idx':
    phi = [(p + SH1) % N for p in range(N)]
    phi2 = [(p + SH2) % N for p in range(N)]
elif MODE == 'geo':
    # sort points and lines by geometric key (dist to a, dist to b, lex), match in order
    pk = sorted(range(N), key=lambda p: (int(dpa[p]), int(dpb[p]), NV[p]))
    lk = sorted(range(N), key=lambda L: (int(dpa[eL[L]]), int(dpb[eL[L]]), NV[int(eL[L])]))
    phi = [0] * N
    for i, p in enumerate(pk):
        phi[p] = lk[i]
    phi2 = [0] * N
    for i, p in enumerate(pk):
        phi2[p] = lk[(i + 1) % N]
    phi2 = phi2
else:
    raise SystemExit('bad mode')

phi_bad = sum((p, phi[p]) in inc for p in range(N))
edges = []
for p in range(N):
    for L in range(N):
        pass
for L in range(N):
    for p in LP[L]:
        edges.append((int(p), L, int(crt(0, int(volt[int(p), L])))))
for p in range(N):
    edges.append((p, phi[p], sig_volt[0]))
    edges.append((p, phi2[p], sig_volt[1]))
# multi-edge check: same (a,b) with same voltage
seen = set()
for a_, b_, v in edges:
    assert (a_, b_, v) not in seen, 'multi-edge'
    seen.add((a_, b_, v))
with open(OUT, 'w') as f:
    f.write(f'{N} {N} {m}\n')
    for a_, b_, v in edges:
        f.write(f'{a_} {b_} {v}\n')
# diversity stats
vals, cnts = np.unique(volt[volt != 0] if False else volt[np.array([(p, L) for L in range(N) for p in LP[L]])[:, 0], np.array([(p, L) for L in range(N) for p in LP[L]])[:, 1]], return_counts=True)
print(f'q={q} N={N} b={b} mode={MODE} CINF={CINF} phi_incidences={phi_bad} sigma_volts={sig_volt} edges={len(edges)} out={OUT}')
print('flag voltage histogram (Z_q):', dict(zip([int(v) for v in vals], [int(c) for c in cnts])))
