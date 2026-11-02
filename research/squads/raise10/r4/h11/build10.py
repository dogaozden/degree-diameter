import sys, itertools
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
vecs = [(x, y) for x in range(3) for y in range(3) if (x, y) != (0, 0)]
vi = {v: i for i, v in enumerate(vecs)}
def vperm(M):
    a, b, c, d = M
    return [vi[((a * x + b * y) % 3, (c * x + d * y) % 3)] for (x, y) in vecs]
M1 = (1, 1, 0, 1); M2 = (0, 2, 1, 0); D2 = (1, 0, 0, 2)
def spec_for(gens):  # gens: list of (matrix, multiplier)
    n = 9 + 8
    maps = [[(i + 1) % 9 if i < 9 else i for i in range(n)]]
    maps += [[(m * i) % 9 if i < 9 else 9 + vperm(M)[i - 9] for i in range(n)] for M, m in gens]
    return "perm %d " % n + " ; ".join(",".join(str(x) for x in mm) for mm in maps)
cands = {}
# Z9 x| GL(2,3) with multiplier -1 (det) on Z9
cands["Z9xGL23det"] = (spec_for([(M1, 1), (M2, 1), (D2, 8)]), 432)
# Z9 x| SL(2,3) with Z3 quotient (multiplier 4^a on M1, 4^b on M2), then x Z2
for a, b in itertools.product(range(3), repeat=2):
    if a == 0 and b == 0:
        continue
    cands["Z9xSL23_%d%d_xZ2" % (a, b)] = (spec_for([(M1, pow(4, a, 9)), (M2, pow(4, b, 9))]) + " x cyc 2", 432)
for name, (spec, o) in cands.items():
    T = groups.table(spec)
    N = len(T)
    print(name, "N=", N, "expected", o, "OK" if N == o else "MISMATCH", flush=True)
    if N == o:
        groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name)
