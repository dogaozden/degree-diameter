# h11 card, third batch: Z3^2 x| (Z8 or Q8) products and small direct products of S3, A4, S4, D_n with Z_k.
import sys
import itertools
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups

def idx(x, y):
    return 3 * (x % 3) + (y % 3)

def lin(M):
    # linear map (x,y) -> M(x,y) on Z3^2, index 3x+y
    a, b, c, d = M
    return [idx(a * (i // 3) + b * (i % 3), c * (i // 3) + d * (i % 3)) for i in range(9)]

def mmul(A, B):
    a, b, c, d = A
    e, f, g, h = B
    return ((a * e + b * g) % 3, (a * f + b * h) % 3, (c * e + d * g) % 3, (c * f + d * h) % 3)

def order(M):
    I = (1, 0, 0, 1)
    P, k = M, 1
    while P != I:
        P = mmul(P, M)
        k += 1
    return k

mats = [m for m in itertools.product(range(3), repeat=4) if (m[0] * m[3] - m[1] * m[2]) % 3 != 0]
# find an element of GL(2,3) of order 8 (Singer-type Z8)
M8 = next(m for m in mats if order(m) == 8)
# find Q8 inside SL(2,3): a of order 4, b of order 4 with b a b^-1 = a^-1 and b^2 = a^2, generating order 8
def gen_group(gens):
    I = (1, 0, 0, 1)
    els = {I}
    frontier = [I]
    while frontier:
        nf = []
        for g in frontier:
            for s in gens:
                h = mmul(g, s)
                if h not in els:
                    els.add(h)
                    nf.append(h)
        frontier = nf
    return els
Q8 = None
sl = [m for m in mats if (m[0] * m[3] - m[1] * m[2]) % 3 == 1]
for a in sl:
    for b in sl:
        if order(a) == 4 and order(b) == 4 and len(gen_group([a, b])) == 8:
            Q8 = (a, b)
            break
    if Q8:
        break
print("M8", M8, "Q8", Q8)

def affine_spec(linmats):
    gens = [[idx(i // 3 + 1, i % 3) for i in range(9)], [idx(i // 3, i % 3 + 1) for i in range(9)]]
    gens += [lin(M) for M in linmats]
    return "perm 9 " + " ; ".join(",".join(str(x) for x in m) for m in gens)

specs = [
    ("Z3^2xZ8tw", affine_spec([M8]) + " x cyc 6", 432),
    ("Z3^2xQ8xZ6", affine_spec(list(Q8)) + " x cyc 6", 432),
    ("S3xS3xA4", "dih 3 x dih 3 x perm 4 1,2,0,3 ; 1,0,3,2", 432),
    ("SL23xS3", "sl2 3 x dih 3", 432),
    ("A4xA4xZ3", "perm 4 1,2,0,3 ; 1,0,3,2 x perm 4 1,2,0,3 ; 1,0,3,2 x cyc 3", 432),
    ("S4xS3xZ3", "perm 4 1,2,3,0 ; 1,0,2,3 x dih 3 x cyc 3", 432),
    ("F21xD10", "perm 7 1,2,3,4,5,6,0 ; 0,2,4,6,1,3,5 x dih 5", 420),
    ("F21xD20", "perm 7 1,2,3,4,5,6,0 ; 0,2,4,6,1,3,5 x dih 10", 420),
    ("D26xD16", "dih 13 x dih 8", 416),
]
with open("/home/user/degree-diameter/research/squads/raise10/r4/h11/specs3.txt", "w") as f:
    for name, spec, order_ in specs:
        T = groups.table(spec)
        N = len(T)
        print(name, "N=", N, "expected", order_, "OK" if N == order_ else "MISMATCH", flush=True)
        groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name)
        f.write(f"{name}|{spec}|{order_}\n")
