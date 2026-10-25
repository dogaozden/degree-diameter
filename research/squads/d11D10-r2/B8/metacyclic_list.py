# B8: primality facts behind the table value 130,592,354 = 2*563*115979, and the metacyclic (Frobenius) groups
# Z_p x| Z_q (q prime, q | p-1) with order p*q in the (11,10) window (74,364,840, 78,917,652].
def sieve(n):
    s = bytearray([1]) * (n + 1)
    s[0] = s[1] = 0
    i = 2
    while i * i <= n:
        if s[i]:
            s[i * i::i] = bytearray(len(range(i * i, n + 1, i)))
        i += 1
    return s

lo, hi = 74_364_840, 78_917_652
S = sieve(hi // 2 + 1)
print("115979 prime:", bool(S[115979]), "| 563 prime:", bool(S[563]),
      "| 563 divides 115979-1:", (115979 - 1) % 563 == 0, "(115979-1 = 115978 = 563*206)")
cands = []
for q in range(2, 400):
    if not S[q]:
        continue
    # p prime with p = 1 mod q and lo < p*q <= hi
    p0 = lo // q + 1
    p1 = hi // q
    p = p0 + ((1 - p0) % q)
    while p <= p1:
        if p >= 3 and S[p]:
            cands.append((p * q, p, q))
        p += q
cands.sort()
print("Frobenius groups Z_p x| Z_q with q prime < 400, q | p-1, order in window: %d" % len(cands))
for c in cands[:12]:
    print("  order %d = p %d * q %d" % c)
