"""Write twist files for twist.c: one collineation lam_c of H(q) per copy (point and line permutations).

usage: mktwist.py hex_qQ.txt C out.bin MODE [seed]
  MODE id            all twists trivial (the thesis graph)
  MODE rand          independent random elements of G_2(q) (random words in SL(3,q) and long root elations)
  MODE perms:FILE    lam_c read from a .npz written by pool.py-style code (keys P, L of shape (C, n))
Every element is a 7x7 matrix checked by geo.Hex.perm to map hexagon lines to hexagon lines."""
import sys, random, numpy as np
sys.path.insert(0, __file__.rsplit('/', 1)[0] if '/' in __file__ else '.')
from geo import Hex


def det3(F, a):
    M, S = F.MUL, lambda x, y: F.ADD[x, F.NEG[y]]
    t1 = M[a[0][0], S(M[a[1][1], a[2][2]], M[a[1][2], a[2][1]])]
    t2 = M[a[0][1], S(M[a[1][0], a[2][2]], M[a[1][2], a[2][0]])]
    t3 = M[a[0][2], S(M[a[1][0], a[2][1]], M[a[1][1], a[2][0]])]
    return int(F.ADD[S(t1, t2), t3])


def rand_sl3(H, rng):
    F = H.F
    while True:
        A = np.array([[rng.randrange(H.q) for _ in range(3)] for _ in range(3)], dtype=np.int64)
        d = det3(F, A)
        if d:
            A[0] = F.MUL[F.INV[d], A[0]]; return A          # det 1: SL(3,q) <= G_2(q)


def rand_elation(H, rng):
    li = rng.randrange(H.n); a, b = H.L[li][0], H.L[li][1]
    lam = rng.randrange(1, H.q)
    v = H.F.MUL[lam, H.P[b]]
    return H.siegel(H.P[a], v)


def rand_elem(H, rng, length=12):
    M = np.eye(7, dtype=np.int64)
    for _ in range(length):
        G = H.sl3(rand_sl3(H, rng)) if rng.random() < 0.5 else rand_elation(H, rng)
        M = H.F.mm(G, M)
    return M


def write(path, Ps, Ls):
    C, n = len(Ps), len(Ps[0])
    with open(path, 'wb') as f:
        np.array([C, n], dtype=np.int32).tofile(f)
        for p, l in zip(Ps, Ls):
            np.asarray(p, dtype=np.int32).tofile(f); np.asarray(l, dtype=np.int32).tofile(f)


if __name__ == '__main__':
    H = Hex(sys.argv[1]); C = int(sys.argv[2]); out = sys.argv[3]; mode = sys.argv[4]
    rng = random.Random(int(sys.argv[5]) if len(sys.argv) > 5 else 1)
    if mode == 'id':
        Ps = [np.arange(H.n)] * C; Ls = [np.arange(H.n)] * C
    elif mode == 'rand':
        Ps, Ls = [], []
        for c in range(C):
            p, l = H.perm(rand_elem(H, rng)) if c else (np.arange(H.n), np.arange(H.n)); Ps.append(p); Ls.append(l)
    elif mode.startswith('perms:'):
        z = np.load(mode[6:]); Ps, Ls = list(z['P']), list(z['L'])
    write(out, Ps, Ls); print('wrote', out, C, 'twists, n =', H.n)
