LO, HI = 1762650, 1790000
N_SIEVE = 1000000
sieve = bytearray([1]) * (N_SIEVE + 1); sieve[0] = sieve[1] = 0
for i in range(2, int(N_SIEVE ** 0.5) + 1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
meta = []
for m in range(3, N_SIEVE + 1, 2):
    if not sieve[m]: continue
    for k in range(3, 200, 2):
        if (m - 1) % k == 0 and m * k <= HI: meta.append((m * k, m, k))
meta.sort()
out = []
for a in meta:
    if a[0] * a[0] > HI: break
    for b in meta:
        if b[0] < a[0]: continue
        N = a[0] * b[0]
        if N > HI: break
        if N >= LO: out.append((N, a, b))
out.sort()
print("odd-k two-factor products:", len(out))
for o in out: print(o)
