LO, HI = 1047481, 1100000
def primes_upto(n):
    s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n + 1) if s[i]]
def pfactors(n):
    f = []; d = 2
    while d * d <= n:
        if n % d == 0:
            f.append(d)
            while n % d == 0: n //= d
        d += 1
    if n > 1: f.append(n)
    return f
out = []
for p in primes_upto(HI // 15 + 2):
    if p < 3: continue
    for k in range(15, HI // p + 1, 2):
        if (p - 1) % k: continue
        N = p * k
        if N < LO or N > HI: continue
        qs = pfactors(k)
        found = None
        for x in range(2, p):
            t = pow(x, (p - 1) // k, p)
            if all(pow(t, k // q, p) != 1 for q in qs):
                found = t; break
        if found is not None: out.append((N, p, k, found))
out.sort()
print(len(out))
for N, p, k, r in out: print(N, p, k, r)
