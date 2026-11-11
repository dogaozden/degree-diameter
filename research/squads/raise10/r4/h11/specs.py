# h11 card: non-metacyclic groups of order 406-432 (cubic Haar graphs, exhaustive via exh3, D = 10).
# Writes one line per group: name|spec|order into specs.txt (the driver script runs groups.py and exh3 on each).
A4 = "perm 4 1,2,0,3 ; 1,0,3,2"
S4 = "perm 4 1,2,3,0 ; 1,0,2,3"
A5 = "perm 5 1,2,3,4,0 ; 1,2,0,3,4"
F21 = "perm 7 1,2,3,4,5,6,0 ; 0,2,4,6,1,3,5"   # Z7 x| Z3 (x -> x+1, x -> 2x)

# generalized dihedral of Z3^2 (inversion), regular on 9 points, index 3x+y
def idx(x, y):
    return 3 * (x % 3) + (y % 3)
tx = [idx(i // 3 + 1, i % 3) for i in range(9)]
ty = [idx(i // 3, i % 3 + 1) for i in range(9)]
inv = [idx(-(i // 3), -(i % 3)) for i in range(9)]
GD9 = "perm 9 " + ",".join(map(str, tx)) + " ; " + ",".join(map(str, ty)) + " ; " + ",".join(map(str, inv))

specs = [
    ("SL23xZ17", "sl2 3 x cyc 17", 408),
    ("A4xZ34", A4 + " x cyc 34", 408),
    ("S4xZ17", S4 + " x cyc 17", 408),
    ("D34xA4", "dih 17 x " + A4, 408),
    ("D34xD12", "dih 17 x dih 6", 408),
    ("A4xZ35", A4 + " x cyc 35", 420),
    ("A5xZ7", A5 + " x cyc 7", 420),
    ("D10xZ2xF21", "dih 5 x cyc 2 x " + F21, 420),
    ("Z2^3xZ52", "cyc 2 x cyc 2 x cyc 2 x cyc 52", 416),
    ("Z2^4xZ26", "cyc 2 x cyc 2 x cyc 2 x cyc 2 x cyc 26", 416),
    ("Z2^3xZ53", "cyc 2 x cyc 2 x cyc 2 x cyc 53", 424),
    ("GD9xZ23", GD9 + " x cyc 23", 414),
    ("D6xZ3xZ23", "dih 3 x cyc 3 x cyc 23", 414),
    ("SL23xZ18", "sl2 3 x cyc 18", 432),
    ("S4xZ18", S4 + " x cyc 18", 432),
    ("A4xZ36", A4 + " x cyc 36", 432),
    ("A4xZ2xZ18", A4 + " x cyc 2 x cyc 18", 432),
    ("A4xZ3xZ12", A4 + " x cyc 3 x cyc 12", 432),
    ("Z2^3xZ54", "cyc 2 x cyc 2 x cyc 2 x cyc 54", 432),
    ("Z3^3xZ16", "cyc 3 x cyc 3 x cyc 3 x cyc 16", 432),
    ("Heis3xZ16", "heis 3 x cyc 16", 432),
    ("S4xZ2xZ3xZ3", S4 + " x cyc 2 x cyc 3 x cyc 3", 432),
]

with open("/home/user/degree-diameter/research/squads/raise10/r4/h11/specs.txt", "w") as f:
    for name, spec, order in specs:
        f.write(f"{name}|{spec}|{order}\n")
print(len(specs), "specs written")
