# enumerate Frobenius Z_p x| Z_k (k | p-1, r of order k mod p) with N = p*k in [35051, 36500], k in 20..63
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
out = []
for N in range(35051, 36501):
    for k in range(20, 64):
        if N % k: continue
        p = N // k
        if not isprime(p) or (p - 1) % k: continue
        # find r of order exactly k mod p, smallest r
        rs = []
        for r in range(2, p):
            if pow(r, k, p) == 1 and all(pow(r, k // q, p) != 1 for q in range(2, k + 1) if k % q == 0 and isprime(q)):
                rs.append(r)
                break
        if rs:
            out.append((N, p, k, rs[0]))
for t in out:
    print("N=%d p=%d k=%d r=%d" % t)
