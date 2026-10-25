# Independent builder: reads hex/hex_q{q}.bin and a lift3 .sol file (GROUP="prod a b"),
# writes the explicit lift as an edge list ("n" then "u v" lines) for research/lifts/coordinator_check/apsp.
# usage: python3 -I build_check.py q sol out_edges
import sys, struct
q, solf, outf = int(sys.argv[1]), sys.argv[2], sys.argv[3]
with open(f"/home/user/degree-diameter/research/d10D8/hex/hex/hex_q{q}.bin", "rb") as f:
    q0, N, L = struct.unpack("<3i", f.read(12))
    assert q0 == q
    Q1 = q + 1
    ln = struct.unpack(f"<{L*Q1}i", f.read(4 * L * Q1))
lines = open(solf).read().split("\n")
qq, J, m, D = map(int, lines[0].split()[:4])
spec = lines[1].split()
assert spec[0] == "prod"
a, b = int(spec[1]), int(spec[2])
assert a * b == m and qq == q
def mul(x, y):   # Z_a x Z_b, element index x = x_a*b + x_b
    return ((x // b + y // b) % a) * b + (x % b + y % b) % b
sig = [list(map(int, lines[2 + t].split())) for t in range(J)]
mv = [list(map(int, lines[2 + J + t].split())) for t in range(J)]
hv = list(map(int, lines[2 + 2 * J].split()))
assert len(hv) == N * Q1 and all(len(s) == N for s in sig)
# sig must be a bijection points -> lines
for t in range(J):
    assert sorted(sig[t]) == list(range(L)), "sigma not a bijection"
E = set()
for l in range(L):
    for k in range(Q1):
        p, g = ln[l * Q1 + k], hv[l * Q1 + k]
        for h in range(m):
            u, w = p * m + h, (N + l) * m + mul(h, g)
            E.add((min(u, w), max(u, w)))
for t in range(J):
    for p in range(N):
        l, g = sig[t][p], mv[t][p]
        for h in range(m):
            u, w = p * m + h, (N + l) * m + mul(h, g)
            E.add((min(u, w), max(u, w)))
nv = 2 * N * m
with open(outf, "w") as f:
    f.write(f"{nv}\n")
    for u, w in sorted(E):
        f.write(f"{u} {w}\n")
print(f"q={q} m={m} D={D} lift vertices={nv} edges={len(E)} expected_edges_if_simple={(L*Q1+J*N)*m} degree_target={Q1+J}")
