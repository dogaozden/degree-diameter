import sys, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d13D7_r5/c1')
import orb8 as L
rng = np.random.default_rng(5)
t = time.process_time()
# 1. transvections preserve Q, are involutions, and preserve B
for _ in range(20):
    v = rng.integers(0, 8, 7).astype(np.int64)
    if int(L.qval(v)) == 0:
        continue
    T = L.transvection(v)
    assert np.array_equal(L.gmm(T, T), L.I7), 'not an involution'
    assert L.is_isom(T), 'not an isometry of Q'
    X = L.P[rng.integers(0, L.N, 300)]
    Y = L.gmm(X, T.T)
    assert np.array_equal(L.bdot(X, X[::-1]), L.bdot(Y, Y[::-1])), 'B not preserved'
print('transvection checks ok')
# 2. orders: |O(7,8)| element orders; a product of random transvections has order dividing NO
ords = []
for _ in range(6):
    g = L.I7.copy()
    for _ in range(int(rng.integers(3, 9))):
        while True:
            v = rng.integers(0, 8, 7).astype(np.int64)
            if int(L.qval(v)): break
        g = L.gmm(L.transvection(v), g)
    assert np.array_equal(L.mpow(g, L.NO), L.I7)
    ords.append(L.order_of(g))
print('random isometry orders', ords)
# 3. perm_of consistency: orbit of a point under g^k equals perm powers
g = L.rand_transv_in(rng, L.I7, 5)
p1 = L.perm_of(g)
m = L.order_of(g)
print('order', m, 'perm is a bijection:', np.array_equal(np.sort(p1), np.arange(L.N)))
pw = np.arange(L.N)
for _ in range(m):
    pw = p1[pw]
assert np.array_equal(pw, np.arange(L.N)), 'perm^order != id'
# 4. baseline 84 set pairwise opposite by bit/table arithmetic
idx = [int(x) for x in open('/home/user/degree-diameter/research/d13D7/q8/R84_q8_idx.txt') if x.strip() and not x.startswith('#')]
print('84-set pairwise_ok:', L.pairwise_ok(idx), len(idx))
# 5. bit-level B agrees with table B
X = L.P[rng.integers(0, L.N, 200)]; Y = L.P[rng.integers(0, L.N, 200)]
Bt = L.bdot(X[:, None, :], Y[None, :, :])
Bb = np.zeros_like(Bt)
for k in range(3):
    S = np.einsum('ai,ij,bj->ab', L.bits(X), L.MATS[k], L.bits(Y))
    Bb |= (np.mod(S, 2).astype(np.int64) << k)
print('bit-level B == table B:', np.array_equal(Bt, Bb))
print('time', round(time.process_time() - t, 2))
