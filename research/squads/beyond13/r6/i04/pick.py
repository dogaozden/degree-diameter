import sys, math
def isp(x):
    if x < 2: return False
    for p in range(2, int(x**0.5)+1):
        if x % p == 0: return False
    return True
lo, hi = int(sys.argv[1]), int(sys.argv[2])
ks = [int(x) for x in sys.argv[3].split(',')]
out = []
for k in ks:
    # m prime, m = 1 mod k ; N = m*k
    m = lo // k + 1
    while m * k <= hi:
        if m * k >= lo and (m - 1) % k == 0 and isp(m):
            # r of order k mod m
            for g in range(2, m):
                r = pow(g, (m - 1) // k, m)
                if r != 1: break
            out.append((m * k, m, k, r))
        m += 1
for N, m, k, r in sorted(out):
    print(N, m, k, r)
