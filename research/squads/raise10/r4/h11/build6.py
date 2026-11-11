import sys, itertools
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
exec(open("/home/user/degree-diameter/research/squads/raise10/r4/h11/build3.py").read().split("specs = [")[0])  # reuse helpers: idx, lin, mmul, order, gen_group, M8
def aff(linmats):
    gens = [[idx(i // 3 + 1, i % 3) for i in range(9)], [idx(i // 3, i % 3 + 1) for i in range(9)]]
    gens += [lin(M) for M in linmats]
    return "perm 9 " + " ; ".join(",".join(str(x) for x in m) for m in gens)
I = (1, 0, 0, 1)
sd16 = None
for g in mats:
    G = gen_group([M8, g])
    if len(G) == 16:
        sd16 = list(G); sd16_gens = [M8, g]; break
D8 = None
for a, b in itertools.combinations(mats, 2):
    G = gen_group([a, b])
    if len(G) == 8 and sum(1 for x in G if x != I and mmul(x, x) == I) == 5:
        D8 = (a, b); break
print("SD16 gens", sd16_gens, "D8 gens", D8, flush=True)
specs = [
    ("Z3^2xSD16xZ3", aff(sd16_gens) + " x cyc 3", 432),
    ("Z3^2xD8xZ6", aff(list(D8)) + " x cyc 6", 432),
    ("S4xD18", "perm 4 1,2,3,0 ; 1,0,2,3 x dih 9", 432),
    ("SL23xD18", "sl2 3 x dih 9", 432),
    ("S4xGD9", "perm 4 1,2,3,0 ; 1,0,2,3 x perm 9 1,2,0,4,5,3,7,8,6 ; 3,4,5,6,7,8,0,1,2 ; 0,2,1,3,5,4,6,8,7", 432),
    ("SL23xS3xZ3", "sl2 3 x dih 3 x cyc 3", 432),
    ("A4xS3xZ6", "perm 4 1,2,0,3 ; 1,0,3,2 x dih 3 x cyc 6", 432),
]
for name, spec, o in specs:
    T = groups.table(spec)
    N = len(T)
    print(name, "N=", N, "expected", o, "OK" if N == o else "MISMATCH", flush=True)
    if N == o:
        groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name)
