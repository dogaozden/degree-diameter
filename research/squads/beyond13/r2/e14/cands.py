import sys
def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    i = 3
    while i * i <= x:
        if x % i == 0: return False
        i += 1
    return True
# odd-order metacyclic Z_m x| Z_k, m prime, k odd prime, 3k | m-1, N = m k (n = 1)
target = float(sys.argv[1])
for k in [19, 31, 37, 43, 61]:
    c = int(target / k)
    best = None
    for m in range(c - 3 * k * 40, c + 3 * k * 40):
        if (m - 1) % (3 * k) == 0 and isprime(m):
            if best is None or abs(m * k - target) < abs(best * k - target): best = m
    if best: print(f"k={k} m={best} N={best*k} ratio={best*k/target:.4f}")
