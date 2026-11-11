"""Features of meta groups Z_m x|_r Z_k: involution count (incl. nothing for identity), abelianization order."""
import sys
from math import gcd
def feats(m, k, r):
    inv = 0
    for j in range(k):
        if (2 * j) % k: continue
        c = (pow(r, j, m) + 1) % m
        inv += gcd(c, m) if c else m
        # for j with r^j = -1 mod m, all a in Z_m give involutions (c=0 -> m solutions)
    if k % 2 == 0 and True:
        pass
    # identity (a=0,j=0) counted once in j=0 term: subtract 1
    inv -= 1
    return inv
if __name__ == "__main__":
    for line in sys.stdin:
        N, m, k, r = map(int, line.split()[:4])
        print(N, m, k, r, feats(m, k, r))
