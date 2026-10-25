"""Hub layout (per-level owners) for x5gen3 from a clhaar solution.

Usage: python3 mkhubs3.py GROUPFILE CLSOL HEXBIN SPREAD.txt PERMSEED OUT.hubs3
The freed set is all points of the spread lines in SPREAD.txt, in that order: freed index = 10*r + t for the t-th
point (hexgen2's order) of the r-th spread line. Line-side hub g (g in Gamma) at level i: its H_i-coset is mapped to a
spread line (coset k -> line perm_i[k]), and inside the coset the pair {y, c_i y} (c_i the subgroup's involution) is
mapped to one point of that line, so each point gets 2 hubs. Point-side hub g at level i: same with K_i, c'_i, and
the owner is the line phi(p) of the chosen point p (x5gen3 looks phi up in the .sol). Hub graph: (g,A) ~ (s g, B).
Output: "HL HP m", HL lines of 5 freed indices, HP lines of 5 freed indices, m lines "j k"."""
import sys, random, struct

def main():
    gfile, sfile, hexbin, spread, seed, out = sys.argv[1:7]
    rng = random.Random(int(seed))
    with open(gfile) as f:
        tok = f.read().split()
    N1, nz, h, nsub = map(int, tok[:4]); pos = 4
    T1 = [list(map(int, tok[pos + a * N1: pos + (a + 1) * N1])) for a in range(N1)]; pos += N1 * N1
    subs = []
    for s in range(nsub):
        c = int(tok[pos]); el = list(map(int, tok[pos + 1: pos + 1 + h])); pos += 1 + h
        subs.append((c, el))
    N = N1 * nz
    def mul(x, y):
        a, z = divmod(x, nz); b, w = divmod(y, nz)
        return T1[a][b] * nz + (z + w) % nz
    st = open(sfile).read().split()
    NN, nz2, d, L = map(int, st[:4]); assert NN == N and nz2 == nz
    S = list(map(int, st[4:4 + d])); lv = list(map(int, st[4 + d: 4 + d + 2 * L]))
    HA, HB = lv[0::2], lv[1::2]
    lines = list(map(int, open(spread).read().split()))
    raw = open(hexbin, 'rb').read(); q, NP, NL = struct.unpack('3i', raw[:12])
    nlines = len(lines)
    def layout(subidx):
        c, H = subs[subidx]
        own = [-1] * N; ncos = 0
        perm = list(range(nlines)); rng.shuffle(perm)
        for y in range(N):
            if own[y] >= 0: continue
            coset = [mul(a, y) for a in H]
            r = perm[ncos]; ncos += 1
            t = 0
            for x in coset:
                if own[x] >= 0: continue
                x2 = mul(c, x)
                own[x] = own[x2] = 10 * r + t; t += 1
            assert t == 10, t
        assert ncos <= nlines
        return own
    ownA = [layout(HA[i]) for i in range(L)]
    ownB = [layout(HB[i]) for i in range(L)]
    E = [(g, mul(s, g)) for g in range(N) for s in S]
    with open(out, "w") as f:
        f.write(f"{N} {N} {len(E)}\n")
        for g in range(N): f.write(" ".join(str(ownA[i][g]) for i in range(L)) + "\n")
        for g in range(N): f.write(" ".join(str(ownB[i][g]) for i in range(L)) + "\n")
        for a, b in E: f.write(f"{a} {b}\n")
    print(f"N={N} hubs per side, {len(E)} hub-graph edges, levels {L} -> {out}")

if __name__ == "__main__":
    main()
