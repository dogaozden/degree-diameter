"""List Q1 x Q2 (x Q3) x Z_n with Q_i = SL(2,q_i) (q_i prime >= 5, or 25/49) and every prime of n == 1 mod 3,
with LO <= |G| <= HI. Used for the (15,9) raise: candidates the two-factor orb_screen.py does not generate.
usage: python3 triple_screen.py LO HI"""
import sys, itertools
lo, hi = int(sys.argv[1]), int(sys.argv[2])
LIM = hi // 120 + 1                      # n is at most hi / (smallest group order 120)
spf = list(range(LIM + 1))
for i in range(2, int(LIM ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j: spf[j] = i
def nok(n):
    while n > 1:
        p = spf[n]
        if p % 3 != 1: return False
        while n % p == 0: n //= p
    return True
def isprime(n): return n > 1 and all(n % p for p in range(2, int(n ** 0.5) + 1))
qs = [(q, q * (q * q - 1)) for q in range(5, 200) if isprime(q)] + [(25, 25 * 624), (49, 49 * 2400)]
out = []
for r in (2, 3):
    for combo in itertools.combinations_with_replacement(qs, r):
        o = 1
        for _, oo in combo: o *= oo
        if o > hi: continue
        n = max(1, -(-lo // o))
        while n * o <= hi:
            if n <= LIM and nok(n): out.append((n * o, n, [q for q, _ in combo]))
            n += 1
for N, n, qq in sorted(out):
    print('N=%d n=%d SL(2,%s)' % (N, n, ') x SL(2,'.join(map(str, qq))))
