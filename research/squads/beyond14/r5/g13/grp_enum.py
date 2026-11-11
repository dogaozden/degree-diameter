def isprime(x):
    if x < 2: return False
    i = 2
    while i*i <= x:
        if x % i == 0: return False
        i += 1
    return True
lo, hi = 866161200, 880000000
out = []
for p in range(5, 1300):
    if not isprime(p): continue
    for name, base in (("psl", p*(p*p-1)//2), ("sl", p*(p*p-1))):
        for n in range(1, 60):
            if n > 1 and p % n == 0: continue
            N = base*n
            if lo < N <= hi:
                out.append((N, name, p, n))
for N, name, p, n in sorted(out):
    print(N, name, p, n)
