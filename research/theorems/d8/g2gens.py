"""Find short-root elements of G_2(q) in the hexq model (beyond the SL(3,q) blocks): x -> u x with
x0' = x0 + 2t x3 + t^2 x4, x3' = x3 + t x4, x5' = x5 + f t x2, x6' = x6 - f t x1 (others fixed), f = +-1,
and the three cyclic coordinate rotations of it.  Prints which variants preserve the line set of H(q)."""
import sys
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import gh
q = int(sys.argv[1])
H = gh.load(q); N = H.N; F = H.F
ADD, MUL, NEG, INV = F.ADD, F.MUL, F.NEG, F.INV
P = np.array(H.P, dtype=np.int64); POW = q ** np.arange(7, dtype=np.int64)
def normalize(V):
    first = np.argmax(V != 0, axis=1); lead = V[np.arange(len(V)), first]
    return MUL[V, INV[lead][:, None]]
code2idx = {int(c): i for i, c in enumerate(normalize(P) @ POW)}
lset = {tuple(sorted(int(p) for p in H.lines[k])) for k in range(N)}
def el(v):  # integer -> field element index (prime field only is enough for 1, 2, -1)
    v %= F.p
    r = 0
    for _ in range(v): r = int(ADD[r, 1])
    return r
def mmul(A, B):
    C = np.zeros((A.shape[0], B.shape[1]), dtype=np.int64)
    for k in range(A.shape[1]): C = ADD[C, MUL[A[:, k][:, None], B[k, :][None, :]]]
    return C
def preserves(G):
    Y = mmul(P, G.T)
    if np.any(np.all(Y == 0, axis=1)): return False
    img = [code2idx.get(int(c), -1) for c in normalize(Y) @ POW]
    if -1 in img: return False
    return all(tuple(sorted(img[int(p)] for p in H.lines[k])) in lset for k in range(N))
t = 1
res = {}
for rot in range(3):
    for f in (1, -1):
        G = np.eye(7, dtype=np.int64)
        a, b, c = rot, (rot + 1) % 3, (rot + 2) % 3   # V3 coords 0,1,2 ; dual 4,5,6
        G[a, 3] = el(2 * t); G[a, 4 + a] = el(t * t); G[3, 4 + a] = el(t)
        G[4 + b, c] = el(f * t); G[4 + c, b] = el(-f * t)
        res[(rot, f)] = preserves(G)
        if res[(rot, f)]: np.save(f'g2_root_q{q}_r{rot}_f{f}.npy', G)
print(q, res)
