"""w16: rebuild the voltage lift (flift convention, (u,x) ~ (v, g x)) of base BASE with voltages VOLT over meta m:k:r
and write the edge list OUT (n = b * |N|, vertex (u,x) = u*N + x). Usage: lift_check.py BASE VOLT M KK R OUT"""
import sys
base, voltf, M, KK, R, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
N = M * KK
lines = open(base).read().split("\n")
b, m = map(int, lines[0].split())
E = [tuple(map(int, lines[1 + i].split()[:2])) for i in range(m)]
V = list(map(int, open(voltf).read().split()))
assert len(V) == m
rp = [pow(R, t, M) for t in range(KK)]
def mul(g, x):  # g, x indices a + M*t
    a, t = g % M, g // M
    c, u = x % M, x // M
    return (a + rp[t] * c) % M + M * ((t + u) % KK)
with open(out, "w") as f:
    f.write(f"{b*N}\n")
    for (u, v), g in zip(E, V):
        for x in range(N):
            f.write(f"{u*N + x} {v*N + mul(g, x)}\n")
print("wrote", out, "n =", b*N, "edges =", m*N)
