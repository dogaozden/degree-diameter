import sys
# usage: pickr.py p k  -> prints elements r of multiplicative order exactly k mod p (prime p)
p, k = int(sys.argv[1]), int(sys.argv[2])
def order(x):
    o, y = 1, x % p
    while y != 1:
        y = y * x % p; o += 1
    return o
out = [x for x in range(2, p) if order(x) == k][:3]
print(" ".join(map(str, out)))
