# enumerate odd meta groups Z_m x|_r Z_k (N = m*k in a window); frob = fixed-point-free action (centre-free, Frobenius-type)
import sys, math
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
lo, hi = int(sys.argv[1]), int(sys.argv[2])
kmin, kmax = int(sys.argv[3]), int(sys.argv[4])
mode = sys.argv[5] if len(sys.argv) > 5 else "all"   # prime | composite | all
out = []
for k in range(kmin, kmax + 1, 2):
    mlo = -(-lo // k); mhi = hi // k
    for m in range(max(3, mlo | 1), mhi + 1, 2):
        isp = isprime(m)
        if mode == "prime" and not isp: continue
        if mode == "composite" and isp: continue
        R = [x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1]
        seen = set()
        for r in R:
            if r in seen: continue
            for t in range(1, k):
                if math.gcd(t, k) == 1: seen.add(pow(r, t, m))
            d = 1; x = r
            while x != 1: x = x * r % m; d += 1
            frob = (d == k) and all(math.gcd((pow(r, j, m) - 1) % m, m) == 1 for j in range(1, k))
            out.append((m * k, m, k, r, d, isp, frob))
out.sort()
for N, m, k, r, d, isp, frob in out:
    print(f"meta {m} {k} {r}\tN={N}\tm={m}\tk={k}\tord_r={d}\tprime_m={int(isp)}\tfrob={int(frob)}")
