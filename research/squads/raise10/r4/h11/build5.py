import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
def idx(x, y):
    return 3 * (x % 3) + (y % 3)
tX = [idx(i // 3 + 1, i % 3) for i in range(9)]
tY = [idx(i // 3, i % 3 + 1) for i in range(9)]
M1 = [idx(i // 3 + i % 3, i % 3) for i in range(9)]
M2 = [idx(2 * (i % 3), i // 3) for i in range(9)]
D2 = [idx(i // 3, 2 * (i % 3)) for i in range(9)]
agl23 = "perm 9 " + " ; ".join(",".join(str(x) for x in m) for m in [tX, tY, M1, M2, D2])
# Z23 x| (S3 x Z3), sign on transposition b; points 0..22 Z23, 23..25 S3 on 3 pts, 26..28 Z3 cycle
n = 29
a3 = [1, 2, 0]; b2 = [1, 0, 2]
t = [(i + 1) % 23 if i < 23 else i for i in range(n)]
ga = [i if i < 23 else (23 + a3[i - 23] if i < 26 else i) for i in range(n)]
gb = [(-i) % 23 if i < 23 else (23 + b2[i - 23] if i < 26 else i) for i in range(n)]
gc = [i if i < 23 else (26 + ((i - 26 + 1) % 3) if i >= 26 else i) for i in range(n)]
s3z3 = "perm %d " % n + " ; ".join(",".join(str(x) for x in m) for m in [t, ga, gb, gc])
# Z23 x| D18 with sign on reflections (rotation acts trivially). D18 = dihedral on a 9-gon, points 23..31
n = 32
r9 = [(j + 1) % 9 for j in range(9)]; s9 = [(-j) % 9 for j in range(9)]
t2 = [(i + 1) % 23 if i < 23 else i for i in range(n)]
gr = [i if i < 23 else 23 + r9[i - 23] for i in range(n)]
gs = [(-i) % 23 if i < 23 else 23 + s9[i - 23] for i in range(n)]
d18 = "perm %d " % n + " ; ".join(",".join(str(x) for x in m) for m in [t2, gr, gs])
specs = [
    ("AGL23", agl23, 432),
    ("Z23xS3xZ3tw", s3z3, 414),
    ("Z23xD18tw", d18, 414),
    ("D53xZ2xZ2", "dih 53 x cyc 2 x cyc 2", 424),
]
for name, spec, o in specs:
    T = groups.table(spec)
    N = len(T)
    print(name, "N=", N, "expected", o, "OK" if N == o else "MISMATCH", flush=True)
    if N == o:
        groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name)
