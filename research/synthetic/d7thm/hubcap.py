#!/usr/bin/env python3
"""Which (q, k) does the hub-graph lemma prove?  (D7_THEOREMS.md, Lemma 4.1 and Theorem 4.4.)

Slot counts (Theorem 3.4, alternating layout, m = q^2+1):
  k = 2a:   K_B = K_A = a (Lam + m)
  k = 2a+1: K_B = a P + (a+1) m,  K_A = a Lam + (a+1) m
with P = (q+1)(q^3+1), Lam = q^4+q^2+q.  The hub graph must be an HG(K_B, K_A; q-k).

Lemma 4.1 (blown-up hexagon): HG(K1, K2; delta) exists if there is a prime power s with
  K0(s) <= K1, K2   and   (s+1) * max(ceil(K1/K0(s)), ceil(K2/K0(s))) <= delta,   K0(s) = (s+1)(s^4+s^2+1).
Lemma 7.1 of D7_HEXAGON.md (plane with pendant trees): HG(K, K; delta) for 7 <= K <= kappa(delta) (equal sides).

For every k = 1..12 and every prime power q <= QMAX this script finds the prime powers q for which neither lemma gives
the full slot counts, and the smallest q_k such that every prime power q >= q_k (q <= QMAX) is covered by Lemma 4.1.
The range q > QMAX is Theorem 4.4(a) (Nagura's theorem); this script also checks the inequality used there.
Output: hubcap.out"""
import math
QMAX = 200000

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    r = int(math.isqrt(n))
    for p in range(3, r + 1, 2):
        if n % p == 0: return False
    return True
def prime_powers(limit):
    sieve = bytearray([1]) * (limit + 1); sieve[0] = sieve[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    pp = set()
    for p in range(2, limit + 1):
        if sieve[p]:
            x = p
            while x <= limit:
                pp.add(x); x *= p
    return sorted(pp)
PP = prime_powers(QMAX)
def K0(s): return (s + 1) * (s ** 4 + s ** 2 + 1)
def slots(q, k, m=None):
    P = (q + 1) * (q ** 3 + 1); Lam = q ** 4 + q ** 2 + q
    if m is None: m = q * q + 1
    a = k // 2
    if k % 2 == 0:
        return a * (Lam + m), a * (Lam + m)
    return a * P + (a + 1) * m, a * Lam + (a + 1) * m
def kappa(d):
    best = 0
    for s in PP:
        if s > d - 1: break
        best = max(best, (s * s + s + 1) * (1 + (d - s - 1) * d))
    return best
def blowup_ok(K1, K2, d):
    """return the s of Lemma 4.1, or None"""
    for s in PP:
        if s + 1 > d: break
        k0 = K0(s)
        if k0 > min(K1, K2): break
        c = max(-(-K1 // k0), -(-K2 // k0))
        if (s + 1) * c <= d:
            return s, c
    return None

out = open('hubcap.out', 'w')
def say(*a):
    s = ' '.join(str(x) for x in a); print(s); out.write(s + '\n'); out.flush()

say('Lemma 4.1 / D7_HEXAGON Lemma 7.1 coverage of the full slot counts, prime powers q <= %d' % QMAX)
for k in range(1, 13):
    fails = []
    for q in PP:
        if q - k < 1: continue
        KB, KA = slots(q, k)
        d = q - k
        ok = blowup_ok(KB, KA, d) is not None
        if not ok and KA == KB and KA <= kappa(d):
            ok = True
        if not ok:
            fails.append(q)
    qk = None
    for q in PP:
        if q - k >= 1 and all(f < q for f in fails):
            qk = q; break
    say('k=%2d: not covered: %s%s ; covered for every prime power q >= %s' % (
        k, fails[:40], ' ...(%d)' % len(fails) if len(fails) > 40 else '', qk))

say('\nexamples (q, k, K_B, K_A, s, blow-up factor c, degree (s+1)c <= q-k):')
for (q, k) in [(11, 2), (13, 2), (16, 2), (11, 3), (13, 3), (16, 3), (13, 4), (32, 2), (37, 2), (64, 2), (101, 2), (101, 3), (101, 4)]:
    KB, KA = slots(q, k)
    say('  q=%d k=%d K_B=%d K_A=%d -> %s (kappa(q-k)=%d)' % (q, k, KB, KA, blowup_ok(KB, KA, q - k), kappa(q - k)))

# Theorem 4.4(a): for q > QMAX use a prime s in (x/1.2, x] with x = K_A^(1/5) - 1 (Nagura: for n >= 25 there is a prime
# in [n, 6n/5]).  Then K0(s) <= K0(x) < K_A <= K_B and K_B / K0(s) < K_B / K0(x/1.2) <= 3 (checked below), so c <= 3,
# and the degree is (s+1)*3 <= 3(x+1) = 3 K_A^(1/5).  Need 3 K_B^(1/5) <= q - k for q > QMAX, 1 <= k <= 12.
say('\nTheorem 4.4(a) inequalities at q = QMAX (both sides increase in the right direction for larger q, see the note):')
for k in range(1, 13):
    q = QMAX
    KB, KA = slots(q, k)
    x = KA ** 0.2 - 1
    ratio = KB / K0(x / 1.2)
    say('  k=%2d: K_B/K0(x/1.2) = %.4f (<= 3), 3*K_B^(1/5) = %.0f <= q-k = %d: %s' % (
        k, ratio, 3 * KB ** 0.2, q - k, ratio <= 3 and 3 * KB ** 0.2 <= q - k))
