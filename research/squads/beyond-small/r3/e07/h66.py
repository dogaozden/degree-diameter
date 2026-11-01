# H = Aut(G) = Z22 (shift g->g+t) x F4* (fibre scalars lam), order 66 (bliss-checked).
import numpy as np
H = 16896; N22 = 22
MUL = np.array([[0,0,0,0],[0,1,2,3],[0,2,3,1],[0,3,1,2]])
def scal_vec(lam):
    # y -> lam*y on F4^4 coded as x0+4x1+16x2+64x3 (2 bits each)
    out = np.zeros(256, dtype=np.int64)
    for y in range(256):
        r = 0
        for k in range(4):
            r |= int(MUL[lam][(y >> (2*k)) & 3]) << (2*k)
        out[y] = r
    return out
SC = [scal_vec(l) for l in range(4)]
def local_perm(lam, t):
    # on local index 0..16895 of one side: blk = 22 j + h, loc = blk*256 + y
    loc = np.arange(H)
    blk, y = loc >> 8, loc & 255
    j, h = blk // N22, blk % N22
    return (j * N22 + (h + t) % N22) * 256 + SC[lam][y]
ELEMS = [(lam, t) for lam in (0,1,2,3) if lam in (0,2,3) for t in range(N22)]  # lam in {0(=1 identity scalar),2(w),3(w^2)}
PERMS = {}
for (lam, t) in [(l, t) for l in (1,2,3) for t in range(N22)]:
    PERMS[(lam, t)] = local_perm(lam, t)
