# Build the 18-regular bipartite route-chart lift from a lift9 parameter file and write the apsp edge list (gzip).
# usage: python3 build_lift9.py PARAMS OUT.edges.gz
import sys, gzip
def main(par, out):
    lines = open(par).read().split("\n")
    p, r, m = map(int, lines[0].split())
    # tpow: t of order r mod p, same rule as lift9.c (smallest x >= 2 with order exactly r)
    t = None
    for x in range(2, p):
        z, ordr = 1, 0
        for e in range(1, r + 1):
            z = z * x % p
            if z == 1:
                ordr = e; break
        if ordr == r:
            t = x; break
    tpow = [pow(t, b, p) for b in range(r)]
    def mul(g, h):
        a1, b1 = divmod(g, r); a2, b2 = divmod(h, r)
        return ((a1 + tpow[b1] * a2) % p) * r + (b1 + b2) % r
    S, A, B = [], [], []
    for ln in lines[1:1 + 9]:
        v = list(map(int, ln.split()))
        S.append(v[0]); A.append(v[1:5]); B.append(v[5])
    def app(cols, x):
        y = 0
        for i in range(4):
            if x >> i & 1: y ^= cols[i]
        return y
    n = 2 * m * 16
    edges = []
    for g in range(m):
        for k in range(9):
            h = mul(S[k], g)
            for x in range(16):
                y0 = app(A[k], x)
                for lam in (0, 1):
                    y = y0 ^ (B[k] if lam else 0)
                    edges.append((g * 16 + x, m * 16 + h * 16 + y))
    with gzip.open(out, "wt") as f:
        f.write(f"{n}\n")
        f.write("\n".join(f"{u} {v}" for u, v in edges))
        f.write("\n")
    print("n", n, "edges", len(edges))
if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
