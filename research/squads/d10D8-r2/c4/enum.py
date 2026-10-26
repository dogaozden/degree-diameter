"""Enumerate G = A x B [x C] x Z_n in the window with haar_sym-buildable factors (sl/psl/pgl q, q prime power)."""
import math, itertools, sys
LO, HI = 588241, 620000
W = 10 * sum(9 ** (2 * i) for i in range(4))          # d=10, D=8 binding words
def pp(q):
    p = None
    for t in range(2, q + 1):
        if q % t == 0: p = t; break
    x = q
    while x % p == 0: x //= p
    return x == 1
qs = [q for q in range(3, 200) if pp(q)]
base = []   # (spec, order, nonabelian?)
for q in qs:
    o = q * (q * q - 1)
    if o <= HI: base.append(('sl %d' % q, o))
    if o <= HI: base.append(('pgl %d' % q, 2 * o if q % 2 else o))
    if q % 2 and o // 2 <= HI: base.append(('psl %d' % q, o // 2))
base = [(s, o) for s, o in base if o >= 12]
# plus smallest: sl 2 (S3, 6), sl 3 (24), psl 3 (12), psl 5 (60): included above (psl 3 = 12, sl 2 -> q=2 not in qs)
base += [('sl 2', 6)]
base = sorted(set(base), key=lambda t: t[1])
out = []
for k in (1, 2, 3):
    for combo in itertools.combinations_with_replacement(range(len(base)), k):
        o = 1
        for i in combo: o *= base[i][1]
        if o > HI: continue
        for n in range(1, 40):
            N = o * n
            if N > HI: break
            if N < LO: continue
            spec = ' x '.join(base[i][0] for i in combo) + ' x Z_%d' % n
            mu = N * math.exp(-W / N)
            out.append((mu, N, k, n, spec))
out.sort()
for mu, N, k, n, spec in out:
    if k >= 2 and n <= 12: print('N=%d mu=%.1f  %s' % (N, mu, spec))
print('total candidates:', len(out))
