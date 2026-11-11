# candidate odd-order products (meta m k) x (meta m2 k2), order N in (LO, HI], sorted ascending by N
import sys
LO, HI = int(sys.argv[1]), int(sys.argv[2])
MAXSMALL = int(sys.argv[3]) if len(sys.argv) > 3 else 200
N_SIEVE = HI  # enough for big factor order <= HI/3
sieve = bytearray([1]) * (N_SIEVE + 1); sieve[0] = sieve[1] = 0
for i in range(2, int(N_SIEVE ** 0.5) + 1):
    if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
groups = []  # (order, m, k)
for m in range(3, N_SIEVE + 1, 2):
    if not sieve[m]: continue
    for k in range(3, 400, 2):
        if (m - 1) % k == 0 and m * k <= N_SIEVE // 3: groups.append((m * k, m, k))
groups.sort()
small = [g for g in groups if g[0] <= MAXSMALL]
out = []
for a in small:
    for b in groups:
        N = a[0] * b[0]
        if N > HI: break
        if N > LO and b[0] >= a[0] and b[2] > 1: out.append((N, a, b))
out.sort()
for o in out: print(o)
