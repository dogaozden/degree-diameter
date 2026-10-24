# pick metacyclic groups Z_p x|_r Z_c (p prime, p = 1 mod 5, r of order 5 mod p, c = 0 mod 5) with N = p*c in a window
import sys
def is_prime(n):
    if n < 2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if n % q == 0: return n == q
    d, s = n-1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(s-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True
def order5_root(p):
    for h in range(2, 1000):
        r = pow(h, (p-1)//5, p)
        if r != 1: return r
lo, hi = int(sys.argv[1]), int(sys.argv[2])
for c in [5, 10, 20, 40]:
    best = None
    for p in range(lo // c, hi // c + 2):
        if p % 5 == 1 and is_prime(p) and lo <= p * c <= hi:
            best = p; break
    if best:
        print(c, best, best * c, order5_root(best), 2 * best * c)
