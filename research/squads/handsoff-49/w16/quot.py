"""w16: quotients of the valid 4,970 Haar graph H(G,S), G = Z_71 x|_49 Z_35 (index a + 71 j), S = {(0,0),(6,18),(30,19),(30,22)}.
Edges (g,A) ~ (s g, B), product (a,j)(b,l) = (a + 49^j b, j + l).
N_k = {(a, k t)} is normal of index k (k | 35); G/N_k = Z_k (via j mod k). The base is H(Z_k, {s_j mod k}) with
2k+2k vertices (k per side) and 4k edges; the voltage group is N_k = meta:71:(35/k):(49^k mod 71).
Voltage (flift convention: edge (u,x) ~ (v, g x), G acts on the right): g = rep_{i'}^{-1} s rep_i, rep_i = (0,i).
Usage: python3 quot.py K OUTBASE OUTVOLT   -> writes base file (b m, then 'u v' lines), volt line (group indices, edge order),
                                             and the group spec in the printout."""
import sys
M, J, R = 71, 35, 49
S = [(0, 0), (6, 18), (30, 19), (30, 22)]

def gmul(x, y):
    return ((x[0] + pow(R, x[1], M) * y[0]) % M, (x[1] + y[1]) % J)

def ginv(x):
    # (a,j)^-1 = (-49^{-j} a, -j)
    inv = pow(R, (-x[1]) % J, M)  # 49^{-j}
    return ((-inv * x[0]) % M, (-x[1]) % J)

def build(k):
    kk = J // k              # order of the cyclic part of N_k
    r = pow(R, k, M)
    NK = M * kk
    def idx(x):              # x in N_k (a, k t) -> index a + M t
        assert x[1] % k == 0, x
        return x[0] + M * (x[1] // k)
    edges = []
    volt = []
    for i in range(k):
        for s in S:
            ip = (s[1] + i) % k
            g = (0, i); h = gmul(s, g)          # s * g_i
            v = gmul(ginv((0, ip)), h)          # rep_{i'}^{-1} s g_i in N_k
            edges.append((i, k + ip))
            volt.append(idx(v))
    return kk, r, NK, edges, volt

if __name__ == "__main__":
    k = int(sys.argv[1]); outb = sys.argv[2]; outv = sys.argv[3]
    kk, r, NK, edges, volt = build(k)
    with open(outb, "w") as f:
        f.write(f"{2*k} {len(edges)}\n")
        for u, v in edges: f.write(f"{u} {v}\n")
    with open(outv, "w") as f:
        f.write(" ".join(map(str, volt)) + "\n")
    print(f"K={k} base {k}+{k} vertices {len(edges)} edges; voltage group meta:{M}:{kk}:{r} order {NK}")
