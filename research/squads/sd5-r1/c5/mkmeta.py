# mkmeta.py: metacyclic group Z_n : Z_k with b a b^-1 = a^r (r^k = 1 mod n), written as .ht (export.g format,
# identity index 0). Element (i,j) = a^i b^j has index i*k+j.  usage: mkmeta.py n k r OUT.ht
import sys
from math import gcd
def build(n, k, r):
    assert pow(r, k, n) == 1 % n and gcd(r, n) == 1
    N = n * k
    rp = [pow(r, j, n) for j in range(k)]
    mul = [[0] * N for _ in range(N)]
    for i in range(n):
        for j in range(k):
            x = i * k + j
            for i2 in range(n):
                for j2 in range(k):
                    y = i2 * k + j2
                    z = ((i + rp[j] * i2) % n) * k + (j + j2) % k
                    mul[x][y] = z
    inv = [0] * N
    for x in range(N):
        for y in range(N):
            if mul[x][y] == 0:
                inv[x] = y
                break
    ninv = sum(1 for x in range(N) if mul[x][x] == 0 and x != 0)
    return N, mul, inv, ninv
if __name__ == "__main__":
    n, k, r = map(int, sys.argv[1:4])
    N, mul, inv, ninv = build(n, k, r)
    with open(sys.argv[4], "w") as f:
        f.write(f"{N} {ninv}\n")
        for row in mul:
            f.write(" ".join(map(str, row)) + "\n")
        f.write(" ".join(map(str, inv)) + "\n")
