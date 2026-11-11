#!/usr/bin/env python3
"""Referee check of the hub-graph certificates of D7_THEOREMS.md, Theorem 4.4(b) and Section 5.2.
Reads hubopt.out (the note's program output) and verifies every line with the note's Lemmas 4.1 and 4.2 only:
  part H(s)xc[A,B]: s a prime power, K0(s) <= A, B <= c K0(s), own degree c(s+1);
  sum of r parts: own degree + r - 1 <= delta = q - k for every part; |A_j| <= |B_i| and |B_j| <= |A_i| for i < j;
  sizes add up to the printed (K1, K2), K1 <= K_B, K2 <= K_A (slot counts recomputed here), FULL iff equal.
Then derives the thresholds q_k (smallest q with FULL for every prime power q' >= q up to 200), and checks the q > 200
range with an own scan of Lemma 4.1 (single blow-up) and Theorem 4.4(a)."""
import re, sys, math

def is_pp(n):
    if n < 2: return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            while n % p == 0: n //= p
            return n == 1
    return True
def K0(s): return (s + 1)*(s**4 + s**2 + 1)
def slots(q, k, m=None):
    if m is None: m = q*q + 1
    P = (q + 1)*(q**3 + 1); Lam = q**4 + q**2 + q; a = k//2
    if k % 2 == 0: return a*(Lam + m), a*(Lam + m)
    return a*P + (a + 1)*m, a*Lam + (a + 1)*m

lines = open(sys.argv[1]).read().splitlines()
res = {}
bad = 0
for ln in lines:
    mo = re.match(r'k=(\d+) q=(\d+)(.*)', ln)
    if not mo: continue
    k, q = int(mo.group(1)), int(mo.group(2))
    if ': none' in ln:
        res[(k, q)] = ('none', 0, 0, ''); continue
    mo2 = re.match(r'k=(\d+) q=(\d+) delta=(\d+) slots=\((\d+),(\d+)\) -> \((\d+),(\d+)\) (FULL|partial): (.*)$', ln)
    k, q, d, T1, T2, K1, K2, tag, desc = mo2.groups()
    k, q, d, T1, T2, K1, K2 = map(int, (k, q, d, T1, T2, K1, K2))
    parts = []
    for p in desc.split(' + '):
        m3 = re.fullmatch(r'H\((\d+)\)x(\d+)\[(\d+),(\d+)\]', p.strip())
        if not m3: print('UNPARSED part', p); bad += 1; continue
        parts.append(tuple(map(int, m3.groups())))
    ok = True; why = []
    if not is_pp(q): ok = False; why.append('q not pp')
    if d != q - k: ok = False; why.append('delta')
    if (T1, T2) != slots(q, k): ok = False; why.append('slots %s' % (slots(q, k),))
    r = len(parts)
    for (s, c, A, B) in parts:
        if not is_pp(s): ok = False; why.append('s not pp')
        if not (K0(s) <= A <= c*K0(s) and K0(s) <= B <= c*K0(s)): ok = False; why.append('sizes H(%d)' % s)
        if c*(s + 1) + r - 1 > d: ok = False; why.append('degree')
    for i in range(r):
        for j in range(i + 1, r):
            if parts[j][2] > parts[i][3] or parts[j][3] > parts[i][2]: ok = False; why.append('order %d,%d' % (i, j))
    if sum(p[2] for p in parts) != K1 or sum(p[3] for p in parts) != K2: ok = False; why.append('sum')
    if not (K1 <= T1 and K2 <= T2): ok = False; why.append('exceeds slots')
    if (tag == 'FULL') != ((K1, K2) == (T1, T2)): ok = False; why.append('tag')
    if not ok: bad += 1; print('BAD', ln[:120], why)
    res[(k, q)] = (tag, K1, K2, ' + '.join('H(%d)%s' % (s, '' if c == 1 else 'x%d' % c) for (s, c, A, B) in parts))
print('certificate lines checked:', sum(1 for v in res.values() if v[0] != 'none'), 'bad:', bad)
# every prime power q <= 200 with q - k >= 2 present?
for k in range(2, 13):
    missing = [q for q in range(2, 201) if is_pp(q) and q - k >= 2 and (k, q) not in res]
    if missing: print('k=%d: no line for q in' % k, missing)
# thresholds
qk = {}
for k in range(2, 13):
    qs = sorted(q for (kk, q) in res if kk == k)
    t = None
    for q in reversed(qs):
        if res[(k, q)][0] == 'FULL': t = q
        else: break
    qk[k] = t
print('thresholds from the certificates (q <= 200):', qk)
claimed = {2: 16, 3: 23, 4: 23, 5: 29, 6: 23, 7: 31, 8: 29, 9: 37, 10: 32, 11: 43, 12: 41}
print('claimed table:', claimed, 'equal:', qk == claimed)

# Lemma 4.1 alone (one blown-up H(s)) for 200 < q <= 2*10^5, 2 <= k <= 12: s prime power, c integer,
# K0(s) <= K_A <= K_B <= c K0(s), c(s+1) <= q - k.  For each s the best c is ceil(K_B/K0(s)); try every s.
import bisect
pps = [s for s in range(2, 60000) if is_pp(s)]
K0s = [K0(s) for s in pps]
fails = []
cnt = 0
cmax = 0
for q in range(201, 200001):
    if not is_pp(q): continue
    for k in range(2, 13):
        KB, KA = slots(q, k); d = q - k
        found = False
        top = bisect.bisect_right(K0s, KA)      # all s with K0(s) <= K_A, tried from the largest down
        assert top < len(pps)
        for i in range(top - 1, -1, -1):
            s = pps[i]
            c = -(-KB // K0(s))
            if c*(s + 1) <= d: found = True; cmax = max(cmax, c); break
        cnt += 1
        if not found: fails.append((q, k))
print('Lemma 4.1 scan, 200 < q <= 2e5, k = 2..12: %d (q, k) pairs, failures: %d %s; largest c used %d' % (cnt, len(fails), fails[:10], cmax))

# Theorem 4.4(a): numeric links of the proof
q = 600
print('q^(4/5) at q=600: %.3f; 1/q^(4/5) = %.5f; 1.2^5 = %.5f; 1.2^5*(1+1/600)/0.97 = %.4f; 3*300^(-1/5) = %.5f' % (
    q**0.8, q**-0.8, 1.2**5, 1.2**5*(1 + 1/600)/0.97, 3*300**-0.2))
import json
json.dump({'%d,%d' % kq: v for kq, v in res.items()}, open('certs.json', 'w'))
