import sys
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
def order_mod(r, p):
    x, o = r % p, 1
    while x != 1:
        x = x * r % p; o += 1
        if o > p: return None
    return o
def meta_list(k, target, span=0.02):
    # primes p with k | p-1, p*k near target; find r of exact order k mod p
    out = []
    lo, hi = int(target / k * (1 - span)), int(target / k * (1 + span)) + 1
    for p in range(max(lo, 3), hi + 1):
        if not isprime(p) or (p - 1) % k: continue
        for r in range(2, p):
            if pow(r, k, p) == 1 and order_mod(r, p) == k:
                out.append((p, k, r, p * k)); break
    return out
if __name__ == "__main__":
    k, target = int(sys.argv[1]), float(sys.argv[2])
    for t in meta_list(k, target, float(sys.argv[3]) if len(sys.argv) > 3 else 0.03)[:6]:
        print("meta %d %d %d  order %d" % t)
