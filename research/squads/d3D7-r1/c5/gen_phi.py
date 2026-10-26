"""gen_phi.py GROUPS id r out: writes phi(g) for a cyclic group of the table as the map x^k -> x^(r k) (N ints).
Checks that phi is an automorphism of order dividing 3."""
import sys
from math import gcd

def load(path, gid):
    tok = open(path).read().split()
    i = 0
    while i < len(tok):
        N, g = int(tok[i + 1]), int(tok[i + 2])
        i += 4
        if g == gid:
            return N, [list(map(int, tok[i + r * N:i + (r + 1) * N])) for r in range(N)]
        i += N * N
    raise SystemExit("group not found")

groups, gid, r, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
N, mul = load(groups, gid)
if r % N == 1 % N or gcd(r, N) != 1 or pow(r, 3, N) != 1 % N:
    if r % N == 1 % N:
        phi = list(range(N))
    else:
        raise SystemExit("r must be a unit with r^3 = 1 mod N")
else:
    phi = None
    for g in range(1, N):
        pw = [0]
        for _ in range(N - 1):
            pw.append(mul[pw[-1]][g])
        if len(set(pw)) == N:
            phi = [0] * N
            for k in range(N):
                phi[pw[k]] = pw[(r * k) % N]
            break
    if phi is None:
        raise SystemExit("group is not cyclic")
for a in range(N):
    for b in range(N):
        assert mul[phi[a]][phi[b]] == phi[mul[a][b]]
assert all(phi[phi[phi[a]]] == a for a in range(N))
open(out, "w").write("\n".join(map(str, phi)) + "\n")
print("N", N, "phi", phi)
