"""Labellings beyond the geometric class, for the audit's evaluator (check/omega_eval), reading 2 (inner P on a-blocks,
L on b-blocks).  Point labellings P_c and line labellings L_c (c >= 1; copy 0 is the identity) are drawn from:
  col   a random collineation (G_2(q) element)            [geometric]
  pol   a random isometry of the quadric Q(6,q) (product of Siegel transformations with random totally singular
        axes): keeps perpendicularity (hexagon distance <= 4 between points) but not the hexagon lines
  rnd   a uniformly random bijection
  id    the identity
usage: polar.py hex_qQ.txt TYPES PMODE LMODE seed out.lab"""
import sys, random, numpy as np
sys.path.insert(0, '.')
from geo import Hex
from mktwist import rand_elem
H = Hex(sys.argv[1]); types = sys.argv[2]; pm, lm = sys.argv[3], sys.argv[4]; rng = random.Random(int(sys.argv[5])); out = sys.argv[6]
F = H.F; n = H.n; C = 5 * len(types)
def rand_isometry(k=20):
    M = np.eye(7, dtype=np.int64)
    for _ in range(k):
        while True:
            a, b = rng.sample(range(n), 2)
            if H.B(H.P[a], H.P[b]) == 0: break
        lam = rng.randrange(1, H.q)
        M = F.mm(H.siegel(H.P[a], F.MUL[lam, H.P[b]]), M)
    return M
def point_perm(M):
    Y = H.normalize(F.mm(H.P, M.T)); pp = H.lut[(Y * H.pwv).sum(1)]; assert (pp >= 0).all(); return pp
Ps, Ls = [], []
for c in range(C):
    if c == 0:
        Ps.append(np.arange(n)); Ls.append(np.arange(n)); continue
    g = None
    if pm == 'col' or lm == 'col': g = H.perm(rand_elem(H, rng, 12))
    P = {'col': lambda: g[0], 'pol': lambda: point_perm(rand_isometry()), 'rnd': lambda: np.array(rng.sample(range(n), n)), 'id': lambda: np.arange(n)}[pm]()
    L = {'col': lambda: g[1], 'rnd': lambda: np.array(rng.sample(range(n), n)), 'id': lambda: np.arange(n)}[lm]()
    Ps.append(P); Ls.append(L)
with open(out, 'w') as f:
    for P in Ps: f.write(' '.join(map(str, P)) + '\n')
    for L in Ls: f.write(' '.join(map(str, L)) + '\n')
