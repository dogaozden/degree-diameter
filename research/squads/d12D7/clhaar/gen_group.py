"""Group data for clhaar: Gamma = G1 x Z_n with G1 = SL(2,p) or PSL(2,p) (p prime), plus candidate subgroups of a
given order h (each with a designated involution for the co-owner pairing).

Usage: python3 gen_group.py sl|psl|pgl q n h NSUB seed OUT.grp     (q prime, or q = 9 = GF(3)[i]/(i^2+1))
Output (text): "N1 n h nsub", then N1 lines of the G1 multiplication table (N1 ints each), then nsub lines
"c e_1 ... e_h": c = the designated involution (Gamma index), then the h elements (Gamma indices, x = a*n + z).
Subgroups: products A x B (A <= G1, B <= Z_n) with |A||B| = h, A taken from closures of random element pairs and
their conjugates. Only subgroups that contain an involution are kept."""
import sys, random, itertools

def main():
    kind, p, n, h, nsub, seed, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), sys.argv[7]
    rng = random.Random(seed)
    q = p
    if q == 9:   # GF(9) = {a + 3b} = a + b i, i^2 = -1
        def fadd(x, y): return (x % 3 + y % 3) % 3 + 3 * ((x // 3 + y // 3) % 3)
        def fmul(x, y):
            a, b, c, d = x % 3, x // 3, y % 3, y // 3
            return (a * c - b * d) % 3 + 3 * ((a * d + b * c) % 3)
    else:
        def fadd(x, y): return (x + y) % q
        def fmul(x, y): return (x * y) % q
    fneg = {x: next(y for y in range(q) if fadd(x, y) == 0) for x in range(q)}
    units = [x for x in range(1, q)]
    def det(m): a, b, c, d = m; return fadd(fmul(a, d), fneg[fmul(b, c)])
    if kind in ("sl", "psl"):
        raw = [m for m in itertools.product(range(q), repeat=4) if det(m) == 1]
    else:
        raw = [m for m in itertools.product(range(q), repeat=4) if det(m) != 0]
    if kind == "psl":
        scal = [x for x in units if fmul(x, x) == 1]
    elif kind == "pgl":
        scal = units
    else:
        scal = [1]
    def canon(m):
        return min(tuple(fmul(s, y) for y in m) for s in scal)
    els = sorted(set(canon(m) for m in raw))
    idx = {m: i for i, m in enumerate(els)}
    N1 = len(els)
    def mul(x, y):
        a, b, c, d = x; e, f, g, k = y
        return canon((fadd(fmul(a, e), fmul(b, g)), fadd(fmul(a, f), fmul(b, k)), fadd(fmul(c, e), fmul(d, g)), fadd(fmul(c, f), fmul(d, k))))
    T = [[idx[mul(x, y)] for y in els] for x in els]
    eid = idx[canon((1, 0, 0, 1))]
    p = q
    inv = [None] * N1
    for i in range(N1):
        for j in range(N1):
            if T[i][j] == eid:
                inv[i] = j; break
    def order(i):
        k, x = 1, i
        while x != eid:
            x = T[x][i]; k += 1
        return k
    def closure(gens):
        S = {eid}; fr = [eid]
        while fr:
            nf = []
            for x in fr:
                for g in gens:
                    y = T[x][g]
                    if y not in S:
                        S.add(y); nf.append(y)
            fr = nf
            if len(S) > 2000: return None
        return S
    # subgroups of G1 of orders dividing h, from random pairs
    subs = {}
    divs = [d for d in range(1, h + 1) if h % d == 0 and n % (h // d) == 0]
    tries = 0
    while tries < 20000 and sum(len(v) for v in subs.values()) < 4000:
        tries += 1
        g1, g2 = rng.randrange(N1), rng.randrange(N1)
        for gens in ([g1], [g1, g2]):
            C = closure(gens)
            if C is None: continue
            if len(C) in divs:
                subs.setdefault(len(C), set()).add(frozenset(C))
    print("G1 subgroups found by order:", {k: len(v) for k, v in sorted(subs.items())}, file=sys.stderr)
    cand = []
    for a, S1 in subs.items():
        m = h // a        # order of the Z_n part
        step = n // m
        B = [step * t for t in range(m)]
        for A in S1:
            G = [x * n + z for x in A for z in B]
            invols = [x * n + z for x in A for z in B if (x != eid or z != 0) and T[x][x] == eid and (2 * z) % n == 0]
            if not invols: continue
            cand.append((invols[0], G))
    rng.shuffle(cand)
    cand = cand[:nsub]
    with open(out, "w") as f:
        f.write(f"{N1} {n} {h} {len(cand)}\n")
        for row in T: f.write(" ".join(map(str, row)) + "\n")
        for c, G in cand: f.write(f"{c} " + " ".join(map(str, sorted(G))) + "\n")
    print(f"{kind} {p} x Z{n}: N1={N1} N={N1 * n}, {len(cand)} candidate subgroups of order {h} -> {out}", file=sys.stderr)

if __name__ == "__main__":
    main()
