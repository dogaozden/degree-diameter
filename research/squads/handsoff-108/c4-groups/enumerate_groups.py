"""c4-groups: enumerate every Q x Z_n that haar_sym2 can build with N = |Q| n in [LO, HI] (k = 3).
usage: python3 enum.py [LO HI] [--prod-meta] > candidates.tsv
Output lines: N <TAB> family <TAB> spec   (spec = haar_sym2 group arguments, the trailing n included)
Base groups (non-abelian): sl q, pgl q, psl q (q odd), agl1 q, meta p k r (p prime, k | p-1, k >= 3, the unique
Z_p x| Z_k). Products: two base groups (--prod-meta: meta allowed as a factor; default: not).
n: 1, or n whose prime factors are all 1 mod 3 (z -> r z, r of order 3, fixes only 0; orb_screen's rule)."""
import sys
LO, HI = 588241, 600000
nums = [a for a in sys.argv[1:] if not a.startswith('--')]
if len(nums) >= 2: LO, HI = int(nums[0]), int(nums[1])
PROD_META = '--prod-meta' in sys.argv
M = HI + 1
spf = list(range(M))
for i in range(2, int(M ** 0.5) + 1):
    if spf[i] == i:
        for j in range(i * i, M, i):
            if spf[j] == j: spf[j] = i
def factor(n):
    f = {}
    while n > 1:
        p = spf[n]; f[p] = f.get(p, 0) + 1; n //= p
    return f
def prime_power(q):
    return q >= 2 and len(factor(q)) == 1
def divisors(n):
    ds = [1]
    for p, e in factor(n).items():
        ds = [d * p ** i for d in ds for i in range(e + 1)]
    return sorted(ds)
def primroot(p):
    fs = list(factor(p - 1).keys())
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs): return g
    return 1

base = []   # (order, tokens, family)
for q in range(2, 800):
    if not prime_power(q): continue
    o = q * (q * q - 1)
    if o <= HI:
        base.append((o, 'sl %d' % q, 'sl'))
        base.append((o, 'pgl %d' % q, 'pgl'))
    if q % 2 and o // 2 <= HI:
        base.append((o // 2, 'psl %d' % q, 'psl'))
    if q > 2 and q * (q - 1) <= HI:
        base.append((q * (q - 1), 'agl1 %d' % q, 'agl1'))
nmeta = 0
for p in range(3, HI // 3 + 1):
    if spf[p] != p: continue
    g = primroot(p)
    for k in divisors(p - 1):
        if k < 3 or p * k > HI: continue
        base.append((p * k, 'meta %d %d %d' % (p, k, pow(g, (p - 1) // k, p)), 'meta')); nmeta += 1
base.sort()
sys.stderr.write('base groups: %d (meta %d)\n' % (len(base), nmeta))

def n_ok(n):
    return n == 1 or all(p % 3 == 1 for p in factor(n))
out = []
def add(order, tok, fam):
    for n in range(max(1, -(-LO // order)), HI // order + 1):
        if n_ok(n): out.append((order * n, fam, '%s %d' % (tok, n)))
for o, tok, fam in base:
    add(o, tok, fam)
npair = 0
for o1, t1, f1 in base:
    if o1 > HI // 2: break
    for o2, t2, f2 in base:
        if o2 < o1: continue
        if o1 * o2 > HI: break
        if not PROD_META and (f1 == 'meta' or f2 == 'meta'): continue
        add(o1 * o2, 'prod %s %s' % (t1, t2), 'prod'); npair += 1
sys.stderr.write('product pairs: %d\n' % npair)
out = sorted(set(out))
out = [x for x in out if LO <= x[0] <= HI]
for N, fam, spec in out:
    print('%d\t%s\t%s' % (N, fam, spec))
sys.stderr.write('candidates: %d\n' % len(out))
