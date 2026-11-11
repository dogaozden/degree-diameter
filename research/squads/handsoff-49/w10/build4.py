"""AGL(2,4) = F_2^4 x| GL(2,4) (order 2880): GL(2,4) as 4x4 matrices over GF(2); F_4 = {0,1,w,w^2} as 2x2 blocks."""
import sys, mk
from build1 import OUT
I2 = ((1, 0), (0, 1)); Z2 = ((0, 0), (0, 0)); W = ((0, 1), (1, 1)); W2 = ((1, 1), (1, 0))  # w, w^2 = w+1
def blk(a, b, c, d):
    M = [[0] * 4 for _ in range(4)]
    for (r0, c0, X) in ((0, 0, a), (0, 2, b), (2, 0, c), (2, 2, d)):
        for i in range(2):
            for j in range(2):
                M[r0 + i][c0 + j] = X[i][j]
    return tuple(tuple(r) for r in M)
gens = [blk(I2, I2, Z2, I2), blk(Z2, I2, I2, Z2), blk(W, Z2, Z2, I2)]
T = None
els, _ = mk.mat_closure(gens, 2)
print("order of GL(2,4) image:", len(els), flush=True)
assert len(els) == 180
T = mk.semidirect_vec(2, 4, gens)
pr = mk.props(T, "AGL24")
mk.write_bin(T, OUT + "AGL24.bin")
print(pr, flush=True)
