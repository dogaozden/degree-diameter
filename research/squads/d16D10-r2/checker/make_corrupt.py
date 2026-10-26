# Writes corrupted copies of the seven test solutions into checker/corrupt/.
#   (a) z of generator 1 changed by +1 (mod n)      [skipped when n = 1: z is always 0]
#   (b) header D lowered by 1
#   (c) generator 1 replaced by a random det-1 matrix (fixed seed), z kept, distinct from all others as PSL elements
import os, random, re, sys

SRC = "/home/user/degree-diameter/research/frontier/sols"
OUT = "/home/user/degree-diameter/research/squads/d16D10-r2/checker/corrupt"
NAMES = ["d6D10_psl_23_38_s1", "d6D10_psl_29_19_s1", "d7D10_psl_29_82_s2",
         "d11D8_psl_59_11_orb5_ORBW5_s3", "d13D8_psl_79_13_s404",
         "d15D8_psl_137_7_orb3f0_s1", "d10D10_psl_389_1_orb3_s1"]
GEN = re.compile(r"^(\S+)\s+mat\((-?\d+),(-?\d+),(-?\d+),(-?\d+)\)\s+z=(-?\d+)\s*$")

def load(path):
    lines = [l.rstrip("\n") for l in open(path)]
    hdr = lines[0].split()
    gens = []
    for l in lines[1:]:
        if not l.strip():
            continue
        m = GEN.match(l)
        assert m, "unparsed line in " + path + ": " + l
        gens.append([m.group(1)] + [int(m.group(i)) for i in range(2, 7)])
    return hdr, gens

def cls(a, b, c, d, p):
    neg = tuple((-x) % p for x in (a, b, c, d))
    t = (a % p, b % p, c % p, d % p)
    return frozenset([t, neg])

def write(path, hdr, gens, p_idx=None):
    with open(path, "w") as f:
        f.write(" ".join(hdr) + "\n")
        for g in gens:
            f.write("%s mat(%d,%d,%d,%d) z=%d\n" % (g[0], g[1], g[2], g[3], g[4], g[5]))

rng = random.Random(20261025)
os.makedirs(OUT, exist_ok=True)
for name in NAMES:
    hdr, gens = load(os.path.join(SRC, name + ".txt"))
    d, D, p, n = int(hdr[0]), int(hdr[1]), int(hdr[3]), int(hdr[5])
    # (a) z + 1
    if n > 1:
        g2 = [list(g) for g in gens]
        g2[1][5] = (g2[1][5] + 1) % n
        write(os.path.join(OUT, name + "__a_z_plus1.txt"), hdr, g2)
    else:
        print("skip (a) for", name, "(n=1)")
    # (b) D - 1
    h2 = list(hdr)
    h2[1] = str(D - 1)
    write(os.path.join(OUT, name + "__b_D_minus1.txt"), h2, gens)
    # (c) random det-1 matrix in place of generator 1 (z kept)
    others = set()
    for j, g in enumerate(gens):
        if j != 1:
            others |= cls(g[1], g[2], g[3], g[4], p) and {(frozenset(cls(g[1], g[2], g[3], g[4], p)), g[5])}
    old = frozenset(cls(gens[1][1], gens[1][2], gens[1][3], gens[1][4], p))
    while True:
        a = rng.randrange(1, p)
        b = rng.randrange(p)
        c = rng.randrange(p)
        d_ = ((1 + b * c) * pow(a, p - 2, p)) % p
        assert (a * d_ - b * c) % p == 1
        k = frozenset(cls(a, b, c, d_, p))
        if k == old or (k, gens[1][5]) in others:
            continue
        break
    g3 = [list(g) for g in gens]
    g3[1][1:5] = [a, b, c, d_]
    write(os.path.join(OUT, name + "__c_randmat.txt"), hdr, g3)
    print("wrote corrupted copies of", name, "(p=%d n=%d d=%d D=%d)" % (p, n, d, D))
