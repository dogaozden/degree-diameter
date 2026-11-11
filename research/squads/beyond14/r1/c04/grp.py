# Writes permutation-generator files (format: "d g" then g lines) for families of groups of order ~2850-3300
# (and PGL/PSL(2,19) for Route B). Usage: python3 grp.py NAME  (or no argument: write all)
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__)); OUT = os.path.join(HERE, "groups")

def pad(g, off, total):
    p = list(range(total))
    for i, x in enumerate(g): p[off + i] = off + x
    return p
def product(factors):           # factors: list of (gens, deg); disjoint-support direct product
    total = sum(dg for _, dg in factors); off = 0; out = []
    for gens, dg in factors:
        for g in gens: out.append(pad(g, off, total))
        off += dg
    return total, out
def cyc(n):
    return ([[(i + 1) % n for i in range(n)]] if n > 1 else []), n
def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in set(f for f in range(2, p) if (p - 1) % f == 0 and all(f % r for r in range(2, f)))):
            return g
    return 1
def psl2_p(p, pgl=False):   # PSL(2,p) (PGL if pgl) on projective line {0..p-1, inf=p}
    T = [(x + 1) % p if x < p else p for x in range(p + 1)]
    S = [p] + [(-pow(x, p - 2, p)) % p for x in range(1, p)] + [0]
    gens = [T, S]
    if pgl:
        g = prim_root(p); gens.append([(g * x) % p if x < p else p for x in range(p + 1)])
    return gens, p + 1
def lin_on_vectors(p, mats):   # matrices acting on F_p^2, points u*p+v
    gens = []
    for M in mats:
        a, b, c, d = M
        gens.append([((a * (i // p) + b * (i % p)) % p) * p + ((c * (i // p) + d * (i % p)) % p) for i in range(p * p)])
    return gens, p * p
def sl2(p, pgl=False):
    mats = [(1, 1, 0, 1), (0, p - 1, 1, 0)]
    if pgl: g = prim_root(p); mats.append((g, 0, 0, 1))
    return lin_on_vectors(p, mats)
def agl1(q):   # q prime
    g = prim_root(q)
    return [[(x + 1) % q for x in range(q)], [(g * x) % q for x in range(q)]], q
def frob(p, k):   # Z_p^2 x| Z_k, Z_k = <zeta> in F_{p^2}^* of order k (p prime, k | p^2-1, k exact order)
    c = next(c for c in range(2, p) if pow(c, (p - 1) // 2, p) == p - 1)
    def mulF(u, v): return ((u[0] * v[0] + c * u[1] * v[1]) % p, (u[0] * v[1] + u[1] * v[0]) % p)
    def powF(u, e):
        r = (1, 0)
        while e:
            if e & 1: r = mulF(r, u)
            u = mulF(u, u); e >>= 1
        return r
    fac = [q for q in range(2, k + 1) if k % q == 0 and all(q % r for r in range(2, q))]
    for a in range(p):
        for b in range(1, p):
            w = powF((a, b), (p * p - 1) // k)
            if powF(w, k) == (1, 0) and all(powF(w, k // q) != (1, 0) for q in fac) and w != (1, 0):
                # matrix of multiplication by w on basis (1, t): (x,y) -> (a x + b c y, b x + a y)
                A, B = w
                M = (A, (B * c) % p, B, A)
                tr = [((i // p + 1) % p) * p + (i % p) for i in range(p * p)]
                tr2 = [(i // p) * p + ((i % p + 1) % p) for i in range(p * p)]
                lin, _ = lin_on_vectors(p, [M])
                return [tr, tr2, lin[0]], p * p
    raise SystemExit("no element")
def metacyc(m, r):   # Z_m x| <r>, acting on Z_m affinely: x -> x+1, x -> r x
    return [[(x + 1) % m for x in range(m)], [(r * x) % m for x in range(m)]], m
def perm_from_gens_list(gens):
    return gens

def order(d, gens):
    seen = {tuple(range(d))}; fr = [tuple(range(d))]
    while fr:
        nf = []
        for g in fr:
            for t in gens:
                h = tuple(g[t[i]] for i in range(d))
                if h not in seen: seen.add(h); nf.append(h)
        fr = nf
    return len(seen)

def A5(): return [[1, 2, 3, 4, 0], [1, 2, 0, 3, 4]], 5
def S4(): return [[1, 2, 3, 0], [1, 0, 2, 3]], 4
def A6(): return [[1, 2, 3, 4, 0, 5], [1, 2, 0, 3, 4, 5]], 6
def sym(n): return [[(i + 1) % n for i in range(n)], [1, 0] + list(range(2, n))], n

def build(name):
    if name == "psl7_z17": t, gens = product([psl2_p(7), cyc(17)])
    elif name == "psl7_z19": t, gens = product([psl2_p(7), cyc(19)])
    elif name == "psl11_z5": t, gens = product([psl2_p(11), cyc(5)])
    elif name == "psl13_z3": t, gens = product([psl2_p(13), cyc(3)])
    elif name == "pgl13_z3": t, gens = product([psl2_p(13, True), cyc(3)])
    elif name == "a5_z49": t, gens = product([A5(), cyc(49)])
    elif name == "a5_z52": t, gens = product([A5(), cyc(52)])
    elif name == "a5_z55": t, gens = product([A5(), cyc(55)])
    elif name == "s4_z120": t, gens = product([S4(), cyc(120)])
    elif name == "s4_z125": t, gens = product([S4(), cyc(125)])
    elif name == "agl29_z4": t, gens = product([agl1(29), cyc(4)])
    elif name == "agl41_z2": t, gens = product([agl1(41), cyc(2)])
    elif name == "agl23_z6": t, gens = product([agl1(23), cyc(6)])
    elif name == "agl13_z21": t, gens = product([agl1(13), cyc(21)])
    elif name == "frob19_8": gens, t = frob(19, 8)
    elif name == "frob19_9": gens, t = frob(19, 9)
    elif name == "frob11_24": gens, t = frob(11, 24)
    elif name == "frob23_6": gens, t = frob(23, 6)
    elif name == "a6_z8": t, gens = product([A6(), cyc(8)])
    elif name == "a6_z9": t, gens = product([A6(), cyc(9)])
    elif name == "sl5_z24": t, gens = product([sl2(5), cyc(24)])
    elif name == "sl5_z25": t, gens = product([sl2(5), cyc(25)])
    elif name == "sl7_z9": t, gens = product([sl2(7), cyc(9)])
    elif name == "pgl7_z9": t, gens = product([sl2(7, True), cyc(9)])
    elif name == "pgl19": gens, t = psl2_p(19, True)
    elif name == "psl19_z2": t, gens = product([psl2_p(19), cyc(2)])
    elif name.startswith("meta_"):   # meta_m_r  (Z_m x| Z_k, k = ord r), e.g. meta_353_2
        _, m, r = name.split("_"); gens, t = metacyc(int(m), int(r))
    else: raise SystemExit("unknown " + name)
    return t, gens

if __name__ == "__main__":
    names = sys.argv[1:]
    os.makedirs(OUT, exist_ok=True)
    for nm in names:
        t, gens = build(nm)
        with open(os.path.join(OUT, nm + ".perm"), "w") as f:
            f.write(f"{t} {len(gens)}\n")
            for g in gens: f.write(" ".join(map(str, g)) + "\n")
        print(nm, "degree", t, "gens", len(gens), "order", order(t, gens))
