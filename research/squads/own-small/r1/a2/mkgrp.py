"""meta:m:k:r table (flift convention) -> gap_export-style single-group text file (no reps line) and optional subgroup .bin.
Usage: python3 mkgrp.py m k r OUT.grp  (element (a,j) = a + m*j, identity 0, product (a,j)(b,l) = (a + r^j b, j+l))"""
import sys
m, k, r, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
N = m * k
rp = [pow(r, j, m) for j in range(k)]
def mul(x, y):
    a, j = x % m, x // m; b, l = y % m, y // m
    return (a + rp[j] * b) % m + m * ((j + l) % k)
with open(out, "w") as f:
    f.write(f"G {N} 1 0\n")
    for x in range(N):
        f.write(" ".join(str(mul(x, y)) for y in range(N)) + "\n")
print("wrote", out, N)
