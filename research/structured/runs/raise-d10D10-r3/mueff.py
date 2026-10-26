import sys, re, math
k = int(sys.argv[1]); f = sys.argv[3]
W = 435848050.0
def factor(n):
    out, p = {}, 2
    while p * p <= n:
        while n % p == 0: out[p] = out.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: out[n] = out.get(n, 0) + 1
    return out
rows = []
for line in open(f):
    m = re.match(r'N=(\d+) 2N=\d+ mu=([\d.]+)\s+(.*)', line)
    if not m: continue
    N, mu, spec = int(m.group(1)), float(m.group(2)), m.group(3).split()
    if len(spec) == 2 and spec[0] == 'prod' or spec[0] == 'prod': continue   # products handled separately
    fam, q, n = spec[0], int(spec[1]), int(spec[2])
    if fam == 'psl':
        order = q * (q * q - 1) // 2
        cands = [(q - 1) // 2, (q + 1) // 2]
    elif fam in ('sl', 'pgl'):
        order = q * (q * q - 1) if fam == 'sl' else q * (q * q - 1)
        cands = [q - 1, q + 1]
    else:
        continue
    # torus containing an element of order k (k must divide the torus order)
    fix = [c for c in cands if c % k == 0]
    if not fix: continue
    fx = fix[0] if fam != 'pgl' else fix[0]
    lam = W / N
    mu_eff = mu / k + fx * math.exp(-lam / k)
    rows.append((mu_eff, N, mu, fx, spec))
rows.sort()
for r in rows[:40]:
    print('mu_eff=%.2f N=%d mu=%.1f fix~%d  %s' % (r[0], r[1], r[2], r[3], ' '.join(r[4])))
