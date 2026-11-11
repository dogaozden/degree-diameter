"""Structured twist files for twist.c (OMEGA_REPAIR.md, Computer-checked 4.2):
  singer   lam_c = s^(e_c), s a Singer cycle of SL(3,q) <= G_2(q) (order q^2+q+1), e_c random
  singerZ  lam_c = s^(c * step)  (an arithmetic progression of exponents)
  elation  lam_c in E_l (long root elations with one hexagon line l as axis; |E_l| = q), lam_c = S(u, a_c v), a_c random
  elation2 lam_c in E_l E_m (l, m two hexagon lines through a point; an abelian group of order q^2)
usage: structured.py hex_qQ.txt C MODE seed out.bin"""
import sys, random, itertools, numpy as np
sys.path.insert(0, '.')
from geo import Hex
from mktwist import write
H = Hex(sys.argv[1]); C = int(sys.argv[2]); mode = sys.argv[3]; rng = random.Random(int(sys.argv[4])); out = sys.argv[5]
F = H.F; q = H.q
def mpow(M, e):
    R = np.eye(7, dtype=np.int64); B = M.copy()
    while e:
        if e & 1: R = F.mm(R, B)
        B = F.mm(B, B); e >>= 1
    return R
def order3(A):
    I = np.eye(3, dtype=np.int64); B = A.copy(); k = 1
    while not (B == I).all():
        B = F.mm(B, A); k += 1
        if k > q ** 3: return -1
    return k
Ps, Ls = [], []
if mode.startswith('singer'):
    for a, b in itertools.product(range(q), repeat=2):
        A = np.array([[0, 0, 1], [1, 0, F.NEG[b]], [0, 1, F.NEG[a]]], dtype=np.int64)
        if order3(A) == q * q + q + 1: break
    S = H.sl3(A); N = q * q + q + 1; step = rng.randrange(1, N)
    for c in range(C):
        e = rng.randrange(N) if mode == 'singer' else (c * step) % N
        p, l = H.perm(mpow(S, e)); Ps.append(p); Ls.append(l)
elif mode.startswith('elation'):
    l0 = H.L[0]; u, v = H.P[l0[0]], H.P[l0[1]]
    p0 = l0[0]; l1 = [li for li in H.lines_of[p0] if li != 0][0]; w = H.P[H.L[l1][1]]
    for c in range(C):
        a = rng.randrange(q); M = H.siegel(u, F.MUL[a, v])
        if mode == 'elation2':
            b = rng.randrange(q); M = F.mm(M, H.siegel(u, F.MUL[b, w]))
        p, l = H.perm(M); Ps.append(p); Ls.append(l)
write(out, Ps, Ls)
