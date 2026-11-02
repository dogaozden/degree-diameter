# h11 card, second batch: twisted semidirect products and affine-type groups, built as permutation groups.
# Writes specs2.txt (name|spec|order) and the table bins are built by build2_tables.py.
import sys
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")


def perm_from_maps(n, maps):
    return "perm %d " % n + " ; ".join(",".join(str(x) for x in m) for m in maps)


def ident_on(n, lo, hi):
    return {i: i for i in range(lo, hi)}


out = []

# 1. Z17 x| S4 with sign action (S4 generators odd, act by x -> -x on Z17). Points 0..16 Z17, 17..20 S4 points.
def twisted(p, base_pts, gens, signs, n_extra_offset, n_total):
    """gens: list of permutations (lists) on base_pts points; signs: multiplier for each gen (as exponent of a)."""
    maps = []
    # translation on Z_p
    t = list(range(n_total))
    for i in range(p):
        t[i] = (i + 1) % p
    maps.append(t)
    for g, mult in zip(gens, signs):
        m = list(range(n_total))
        for i in range(p):
            m[i] = (mult * i) % p
        for j in range(base_pts):
            m[p + j] = p + g[j]
        maps.append(m)
    return maps

S4g = [[1, 2, 3, 0], [1, 0, 2, 3]]
A4g = [[1, 2, 0, 3], [1, 0, 3, 2]]
sgnS4 = [p_ for p_ in [16, 16]]  # -1 mod 17 is 16
m17 = twisted(17, 4, S4g, [16, 16], 0, 21)
out.append(("Z17xS4tw", perm_from_maps(21, m17), 408))

# 2. Z7 x| (A4 x Z5): A4 acts on Z7 through A4 -> Z3, a (3-cycle) -> mult 2, b (double transp) -> mult 1. Z5 direct.
n = 16
maps = []
t7 = [(i + 1) % 7 if i < 7 else i for i in range(n)]
maps.append(t7)
a_ = [2 * i % 7 if i < 7 else (7 + A4g[0][i - 7]) if i < 11 else i for i in range(n)]
b_ = [i if i < 7 else (7 + A4g[1][i - 7]) if i < 11 else i for i in range(n)]
z5 = [i if i < 11 else 11 + ((i - 11 + 1) % 5) for i in range(n)]
maps += [a_, b_, z5]
out.append(("Z7xA4xZ5tw", perm_from_maps(n, maps), 420))

# 3. Z23 x| GD9 with sign: GD9 = Z3^2 x| Z2 (inversion); inversion acts by -1 on Z23, translations trivially.
def idx(x, y):
    return 3 * (x % 3) + (y % 3)
tx = [idx(i // 3 + 1, i % 3) for i in range(9)]
ty = [idx(i // 3, i % 3 + 1) for i in range(9)]
inv9 = [idx(-(i // 3), -(i % 3)) for i in range(9)]
n = 32
maps = []
maps.append([(i + 1) % 23 if i < 23 else i for i in range(n)])
maps.append([i if i < 23 else 23 + tx[i - 23] for i in range(n)])
maps.append([i if i < 23 else 23 + ty[i - 23] for i in range(n)])
maps.append([(-i) % 23 if i < 23 else 23 + inv9[i - 23] for i in range(n)])
out.append(("Z23xGD9tw", perm_from_maps(n, maps), 414))

# 4. Z53 x| D8 with sign: r (4-cycle) -> -1, s (reflection (1 3)) -> +1. Kernel <r^2, s> = V4.
n = 57
maps = [[(i + 1) % 53 if i < 53 else i for i in range(n)]]
r4 = [1, 2, 3, 0]
s4 = [0, 3, 2, 1]
maps.append([(-i) % 53 if i < 53 else 53 + r4[i - 53] for i in range(n)])
maps.append([i if i < 53 else 53 + s4[i - 53] for i in range(n)])
out.append(("Z53xD8tw", perm_from_maps(n, maps), 424))

# 5. Z17 x| D24 with sign on rotations (kernel <r^2, s>). D24 = dih 12 on a 12-gon.
n = 29
r12 = [(j + 1) % 12 for j in range(12)]
s12 = [(-j) % 12 for j in range(12)]
maps = [[(i + 1) % 17 if i < 17 else i for i in range(n)]]
maps.append([(-i) % 17 if i < 17 else 17 + r12[i - 17] for i in range(n)])
maps.append([i if i < 17 else 17 + s12[i - 17] for i in range(n)])
out.append(("Z17xD24tw", perm_from_maps(n, maps), 408))

# 6. Z13 x| D32 with sign on rotations (kernel <r^2, s>), D32 = dih 16 on a 16-gon.
n = 29
r16 = [(j + 1) % 16 for j in range(16)]
s16 = [(-j) % 16 for j in range(16)]
maps = [[(i + 1) % 13 if i < 13 else i for i in range(n)]]
maps.append([(-i) % 13 if i < 13 else 13 + r16[i - 13] for i in range(n)])
maps.append([i if i < 13 else 13 + s16[i - 13] for i in range(n)])
out.append(("Z13xD32tw", perm_from_maps(n, maps), 416))

# 7. ASL(2,3) x Z2 (order 432): affine group on Z3^2 (index 3x+y) x Z2.
tX = [idx(i // 3 + 1, i % 3) for i in range(9)]
tY = [idx(i // 3, i % 3 + 1) for i in range(9)]
M1 = [idx(i // 3 + i % 3, i % 3) for i in range(9)]      # (x,y) -> (x+y, y)
M2 = [idx(2 * (i % 3), i // 3) for i in range(9)]        # (x,y) -> (2y, x)
asl = "perm 9 " + " ; ".join(",".join(str(x) for x in m) for m in [tX, tY, M1, M2])
out.append(("ASL23xZ2", asl + " x cyc 2", 432))

# 8. Z3 x| ... control: Z3^2 x| Q8-like is skipped. Z7 x| (Z3 x S3 type)  not included.

with open("/home/user/degree-diameter/research/squads/raise10/r4/h11/specs2.txt", "w") as f:
    for name, spec, order in out:
        f.write(f"{name}|{spec}|{order}\n")
print(len(out), "specs written")
