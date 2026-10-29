"""The exact whisker set of POLISHED.md Theorem 6.5 for H(11), and the dual segment set R_L = L_v + W.

Coordinates as POLISHED.md 6.1 (and hex_q11.bin): Q(6,q): X0X4 + X1X5 + X2X6 = X3^2, Tits' equations.  q = 11, c = 1
(-c = -1 is a non-square), (c0, c1) = (1, 3).  v = <e1, e6>; Pi_z: X0 + c X4 + a X2 + b X5 = 0, Pi = Pi_(0,0) (the
hyperplane x4 = -x0 of the Hermitian spread S); S_z = lines of H(q) in Pi_z.
  nu(X) = (X2 X3 - X4 X5) / (c X2^2 + X5^2),  G(a,b) = (c0 a + c1 b)(a^2 + c b^2) - b^3,  F(z) = G(a,b)/(a^2 + c b^2),
  W = { l in S_z, l != v : z != 0, nu(l cap Pi) = F(z) }.
Checks: |W| = q^2 (q^2 - 1), every free point (off Pi, at distance 5 from v) on exactly one line of W, whiskers opposite
v and not in S.  Then R_L = (lines != v meeting v) + W, written to RL_whisk.txt (a dual segment set: two of its lines
meet only in a point of Pi, which is the one point of Pi on each of them).
"""
import numpy as np

b = open('/home/user/degree-diameter/research/p4/d6/hex/hex_q11.bin', 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32))
Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
X = np.frombuffer(b[12 + 4 * Lc * Q1:], dtype=np.uint8).reshape(N, 7).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
order = np.lexsort((flat_l, flat_p)); PL = flat_l[order].reshape(N, Q1)
c, c0, c1 = 1, 1, 3
assert pow(-c % q, (q - 1) // 2, q) == q - 1, '-c must be a non-square'
inv = [0] + [pow(a, q - 2, q) for a in range(1, q)]

# v = <e1, e6>
e1 = np.nonzero((X == np.array([0, 1, 0, 0, 0, 0, 0])).all(1))[0][0]
e6 = np.nonzero((X == np.array([0, 0, 0, 0, 0, 0, 1])).all(1))[0][0]
(v,) = set(PL[e1]) & set(PL[e6])
print('v =', v)
inPi = (X[:, 0] + c * X[:, 4]) % q == 0
S = np.nonzero(inPi[LP].all(1))[0]
assert len(S) == q ** 3 + 1 and v in S


def G(a, bb):
    return ((c0 * a + c1 * bb) * (a * a + c * bb * bb) - bb ** 3) % q


for a in range(q):
    for bb in range(q):
        if (a, bb) != (0, 0):
            assert G(a, bb) != 0, 'G has a zero'
W = []
for a in range(q):
    for bb in range(q):
        if (a, bb) == (0, 0):
            continue
        inPz = (X[:, 0] + c * X[:, 4] + a * X[:, 2] + bb * X[:, 5]) % q == 0
        Sz = np.nonzero(inPz[LP].all(1))[0]
        assert len(Sz) == q ** 3 + 1 and v in Sz
        F = G(a, bb) * inv[(a * a + c * bb * bb) % q] % q
        for l in Sz:
            if l == v:
                continue
            pts = LP[l][inPi[LP[l]]]
            assert len(pts) == 1
            x = X[pts[0]]
            num = (x[2] * x[3] - x[4] * x[5]) % q
            den = (c * x[2] * x[2] + x[5] * x[5]) % q
            assert den != 0
            if num * inv[den] % q == F:
                W.append(int(l))
W = np.array(sorted(set(W)), dtype=np.int64)
print('|W| =', len(W), 'expected', q * q * (q * q - 1))
# points at distance <= 3 from v: X2 = X5 = 0 (Lemma 6.1(d)); free points: off Pi and not at distance <= 3
near = (X[:, 2] % q == 0) & (X[:, 5] % q == 0)
free = ~inPi & ~near
print('free points', free.sum(), 'expected', q ** 3 * (q * q - 1))
cnt = np.zeros(N, np.int64)
np.add.at(cnt, LP[W].reshape(-1), 1)
assert (cnt[free] == 1).all(), 'not exact'
assert not np.isin(W, S).any()
assert not near[LP[W]].any(), 'a whisker has a point at distance <= 3 from v'
print('exact whisker set: every free point on exactly one whisker')
Lv = np.array(sorted(set(PL[LP[v]].reshape(-1)) - {v}), dtype=np.int64)
assert len(Lv) == q * q + q
RL = np.concatenate([Lv, W])
open('RL_whisk.txt', 'w').write('\n'.join(str(l) for l in RL) + '\n')
print('R_L = L_v + W:', len(RL), 'lines; wrote RL_whisk.txt')
