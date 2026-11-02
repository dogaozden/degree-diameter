import sys, itertools
sys.path.insert(0, "/home/user/degree-diameter/research/squads/raise10/tools")
import groups
vecs = [(x, y) for x in range(3) for y in range(3) if (x, y) != (0, 0)]
vi = {v: i for i, v in enumerate(vecs)}
def vperm(M):
    a, b, c, d = M
    return [vi[((a * x + b * y) % 3, (c * x + d * y) % 3)] for (x, y) in vecs]
M8 = (0, 1, 1, 1); g8 = (0, 1, 2, 0); a8 = (0, 1, 1, 0)
def build(m, mats, mults, extra=""):
    n = m + 8
    maps = [[(i + 1) % m if i < m else i for i in range(n)]]
    for M, k in zip(mats, mults):
        maps.append([(k * i) % m if i < m else m + vperm(M)[i - m] for i in range(n)])
    return "perm %d " % n + " ; ".join(",".join(str(x) for x in mm) for mm in maps) + extra
cands = {}
for mults in itertools.product([1, -1], repeat=2):
    cands["Z27xSD16_%s" % ("".join("p" if k == 1 else "m" for k in mults))] = (build(27, [M8, g8], mults), 432)
    cands["Z9xSD16_%s_xZ3" % ("".join("p" if k == 1 else "m" for k in mults))] = (build(9, [M8, g8], mults, " x cyc 3"), 432)
for mults in itertools.product([1, -1], repeat=2):
    cands["Z27xD8_%s_xZ2" % ("".join("p" if k == 1 else "m" for k in mults))] = (build(27, [M8, a8], mults, " x cyc 2"), 432)
for name, (spec, o) in cands.items():
    T = groups.table(spec)
    N = len(T)
    print(name, "N=", N, "expected", o, "OK" if N == o else "MISMATCH", flush=True)
    if N == o:
        groups.write_bin(T, "/home/user/degree-diameter/research/squads/raise10/r4/h11/%s.bin" % name)
