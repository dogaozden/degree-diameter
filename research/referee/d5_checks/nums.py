"""Recompute the numbers of D5_QUADRANGLE.md (sec. 0, 7, 8, 9, 10, 12, 14) independently."""
import math
N = lambda q: (q + 1) * (q * q + 1)
pp = [q for q in range(2, 40) if len({p for p in range(2, q + 1) if q % p == 0 and all(p % d for d in range(2, p))}) == 1]
print("prime powers:", pp)
table = {10: 4000, 11: 5850, 12: 8200, 13: 11480, 14: 14760, 15: 20496, 16: 27300}
# sec. 0: table values = (2r+1) 2 N(q)
for D, (q, r) in {10: (7, 2), 11: (8, 2), 12: (9, 2), 13: (9, 3), 14: (9, 4), 15: (11, 3)}.items():
    print("(%d,5): (2r+1)*2N(%d) = %d, table %d, degree q+1+r = %d" % (D, q, (2 * r + 1) * 2 * N(q), table[D], q + 1 + r))
# which (q,r) give exactly the table value (and the largest (2r+1)2N(q) with q+1+r = Delta)?
for D in range(10, 17):
    vals = [((2 * r + 1) * 2 * N(q), q, r) for q in pp for r in range(1, 20) if q + 1 + r == D]
    print("  Delta=%d: largest (2r+1)2N(q) = %s; table %d" % (D, max(vals), table[D]))

# Lemma 9.1: set of (KB, KA) available at max degree delta (balanced or not) -- feasibility test
def hg_ok(KB, KA, d):
    if KB < 1 or KA < 1:
        return False
    if KB <= d and KA <= d:
        return True                                                       # Y0
    for s in pp:
        if s + 1 <= d:
            P = s * s + s + 1
            if P <= KB <= P * (d - s) and P <= KA <= P * (d - s):
                return True                                               # Y1
            if N(s) <= KB <= N(s) + (s + 1) * (d - s - 1) and N(s) <= KA <= N(s) + (s + 1) * (d - s - 1):
                return True                                               # Y2
        for rp in range(1, 10):
            if s + 1 + rp <= d and KB == KA == (2 * rp + 1) * N(s):
                return True                                               # Y3
    return False
def best_hubs(maxB, maxA, d):
    best = None
    for KB in range(1, maxB + 1):
        for KA in range(1, maxA + 1):
            if hg_ok(KB, KA, d) and (best is None or KB + KA > best[0]):
                best = (KB + KA, KB, KA)
    return best
# Cor 10.1 (q even), 10.2-10.4 (q odd >= 5): best value per Delta
res = {}
for q in pp:
    if q > 30:
        continue
    cands = []
    if q % 2 == 0:
        for r in range(1, q):
            mx = r * (q * q + 1)
            b = best_hubs(min(mx, 400), min(mx, 400), q - r)
            if b:
                cands.append((q + 1 + r, (2 * r + 1) * 2 * N(q) + b[0], '10.1', r, b))
    elif q >= 5:
        a, bb, c = q * q + 1, 3 * q - 1, 2
        for cor, r, mB, mA in (('10.2', 2, bb + c, bb + c), ('10.3', 3, min(a + 2 * c, 2 * bb + c, 3 * bb), bb + 2 * c),
                               ('10.4', 4, min(a + 3 * c, 3 * bb + c, 4 * bb), bb + 3 * c)):
            if q - r >= 1:
                b = best_hubs(mB, mA, q - r)
                if b:
                    cands.append((q + 1 + r, (2 * r + 1) * 2 * N(q) + b[0], cor, r, b))
    for D, v, cor, r, b in cands:
        if D not in res or v > res[D][0]:
            res[D] = (v, q, cor, r, b)
for D in range(10, 17):
    v, q, cor, r, b = res[D]
    print("theorem family (%d,5): %d  (Cor %s, q=%d, r=%d, KB+KA=%d with KB=%d, KA=%d)  table %d  %s" %
          (D, v, cor, q, r, b[0], b[1], b[2], table[D], "beats" if v > table[D] else "below"))
# Cor 10.3: min(q^2+5, 6q) = 6q for q >= 5
print("Cor 10.3: q^2+5 >= 6q for all q>=5:", all(q * q + 5 >= 6 * q for q in range(5, 1000)))
print("Cor 10.4: min(q^2+7, 9q-1):", [(q, min(q * q + 7, 9 * q - 1)) for q in (5, 7, 9, 11, 13)])
# sec. 7 counting bound 2(q+1)(q^2+1)/(2q+1)
for q in (5, 7, 9, 11):
    print("relaxed-set counting bound q=%d: %.2f -> %d" % (q, 2 * N(q) / (2 * q + 1), 2 * N(q) // (2 * q + 1)))
# sec. 11 slots
a, b, c = 82, 66, 2
print("record: alpha =", (a + 2 * c, 2 * b + c, 3 * b), "beta =", (b + 2 * c, 3 * a, 2 * a + c), "n =", 14 * N(9) + a + 2 * c + b + 2 * c)
for bb in (51, 56, 57):
    print("  with b=%d, c=2: n <= %d; c=0: n <= %d" % (bb, 14 * N(9) + min(a + 4, 2 * bb + 2, 3 * bb) + bb + 4,
                                                      14 * N(9) + min(a, 2 * bb, 3 * bb) + bb))
# sec. 12 heuristic
for q in (5, 7, 9, 11):
    n_ = N(q); f = math.exp(-1) * math.exp(-5 * (q + 1) ** 2 / n_)
    print("sec 12 heuristic q=%d: N/e = %.0f, uncovered fraction %.3f, pairs per freed element %.0f; exact (1-(q+1)/N)^(q(q+1)) = %.3f"
          % (q, n_ / math.e, f, f * n_, (1 - (q + 1) / n_) ** (q * (q + 1))))
# sec. 14 (15,5)
a, c = 122, 2
need = 20736 - 14 * N(11) + 1
bmin = next(b for b in range(1, 200) if min(a + 2 * c, 2 * b + c, 3 * b) + b + 2 * c >= need)
print("(15,5): to beat 20,736 need KA+KB >= %d, i.e. b >= %d; Tallini q^2-q+1 = %d; 87 gives %d; 70 gives %d" %
      (need, bmin, 121 - 11 + 1, 14 * N(11) + min(126, 176, 261) + 91, 14 * N(11) + 126 + 74))
print("  23/28 = %.3f, 0.82*127 = %.1f" % (23 / 28, 23 / 28 * 127))
# Lemma 9.1 balanced maxima (squad card c10 list), delta = 2..12
print("balanced HG_5 maxima from Lemma 9.1, delta=3..12:",
      [max(K for K in range(1, 5000) if hg_ok(K, K, d)) for d in range(3, 13)])
# DM lifts 12 N(q) at degree q+3
print("12N(q):", {q + 3: 12 * N(q) for q in (7, 8, 9, 11)})
