import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
# V = F2^4 as integers 0..15 (bit k = coordinate k). Linear maps over F2 given as 4x4 bit matrices (columns = images of e_k).
def apply(cols, v):
    out = 0
    for k in range(4):
        if (v >> k) & 1:
            out ^= cols[k]
    return out
W = [0b10, 0b11]  # mult by omega on F4 = F2^2 in basis (1, omega): 1->omega (bit1), omega->omega^2=omega+1 (bits 0,1)
def blk(a_cols2, b_cols2):  # block diag on coords (0,1) and (2,3)
    return [a_cols2[0], a_cols2[1], b_cols2[0] << 2, b_cols2[1] << 2]
I2 = [0b01, 0b10]
L1 = blk(W, I2)
L2 = blk(I2, W)
# sanity: L1 order 3
def tr(cols):
    return [apply(cols, v) for v in range(16)]
def perm_V(cols, extra):  # permutation of the 16 points plus identity on extra points
    return tr(cols) + list(range(16, 16 + extra))
def trans(k):
    return [v ^ (1 << k) for v in range(16)]
# G1: (Z2^4 x| Z3^2) x Z3, points 0..15 V, 16..18 Z3 cycle
n = 19
gens = [trans(k) + [16, 17, 18] for k in range(4)]
gens += [perm_V(L1, 3), perm_V(L2, 3)]
gens += [list(range(16)) + [17, 18, 16]]
s1 = "perm %d " % n + " ; ".join(",".join(str(x) for x in g) for g in gens)
# G4: (Z2^4 x| Z9) x Z3 with Z9 acting by omega-scalar (diag(omega,omega)), points 16..24 cycle; Z3 direct on 25..27
W2 = blk(W, W)  # scalar omega on F4^2
n2 = 28
gens4 = [trans(k) + list(range(16, 28)) for k in range(4)]
gens4 = [g[:16] + list(range(16, 28)) for g in gens4]
gens4 = [trans(k) + list(range(16, 28)) for k in range(4)]
gens4.append(tr(W2) + [16 + ((i + 1) % 9) for i in range(9)] + [25, 26, 27])
gens4.append(list(range(16)) + [16 + ((i + 1) % 9) for i in range(9)] + [25, 26, 27])
gens4.append(list(range(16)) + list(range(16, 25)) + [26, 27, 25])
s4 = "perm %d " % n2 + " ; ".join(",".join(str(x) for x in g) for g in gens4)
specs = [("V4xZ3sq_G1", s1, 432), ("V4xZ9_G4", s4, 432)]
for name, spec, o in specs:
    T = groups.table(spec)
    N = len(T)
    print(name, "N=", N, "expected", o, "OK" if N == o else "MISMATCH", flush=True)
    if N == o:
        groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name)
