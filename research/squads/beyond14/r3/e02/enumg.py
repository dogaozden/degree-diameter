import math
def isprime(n):
    return n > 1 and all(n % p for p in range(2, int(n**0.5) + 1))
out = []; seen = set()
for N in range(1752, 1801):
    for k in range(9, N + 1):
        if N % k: continue
        m = N // k
        if m < 2: continue
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            o = 1; x = r
            while x != 1: x = x * r % m; o += 1
            if o == 1: continue
            frob = isprime(m) and o == k
            if not (frob or o < k): continue
            sub = tuple(sorted(pow(r, j, m) for j in range(o)))
            if (m, k, sub) in seen: continue
            seen.add((m, k, sub))
            out.append((N, m, k, r, o, 'F' if frob else 'N'))
out.sort(key=lambda t: (t[5] != 'F', t[0]))
print(len(out))
for t in out: print(*t)
