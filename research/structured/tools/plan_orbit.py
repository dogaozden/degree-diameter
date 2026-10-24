"""Plan orbit runs with the clumped-Poisson model of research/theory/BEYOND_RANDOM.md (branch cd-theory-beyond-random):
mu_A = mu/k + (fixed-point term), predicted evals = 1e5 exp((mu_A - 13)/2) (scatter about x5), time = evals * c * N.
usage: python3 plan_orbit.py d D LO HI [--k 3,5] [--frob] [--fams sl,psl,pgl] [--nmax 400] [--nq 6] [--c 4e-9]
                             [--hours 4] [--top 40]
LO, HI are vertex counts (2N). Lists Q x Z_n (Q = SL/PSL/PGL(2,q); SL only at odd D), every prime of n = 1 mod k,
n <= nq * q, with alpha = conjugation of order k (Fix = a torus, or Z(Q) x U when p = k), and with --frob also
Frobenius of order k on GF(p^e) (k | e; Fix = Q(2, p^(e/k))). Ranked by vertices among the runs whose predicted time
fits in --hours single-thread hours (c = seconds per element per evaluation, 2.2-5 ns measured here with 4 jobs)."""
import sys, math
args = sys.argv[1:]
d, D, lo, hi = int(args[0]), int(args[1]), int(args[2]), int(args[3])
opt = {'k': '3,5', 'fams': 'sl,psl,pgl', 'nmax': '400', 'nq': '6', 'c': '3e-9', 'hours': '4', 'top': '40'}
flags = set(); i = 4
while i < len(args):
    if args[i] in ('--frob', '--all'): flags.add(args[i][2:]); i += 1
    else: opt[args[i][2:]] = args[i + 1]; i += 2
ks = [int(x) for x in opt['k'].split(',')]
fams = opt['fams'].split(',') if D % 2 == 0 else ['sl']
def W(d, D):
    if D % 2: kk = (D - 1) // 2; return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, kk + 1))
    kk = D // 2; return d * sum((d - 1) ** (2 * i) for i in range(kk))
def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def pp(q):
    f = factor(q); return (list(f.items())[0] if len(f) == 1 else None)
def order(fam, q): return q * (q * q - 1) // (2 if fam == 'psl' else 1)
def conj_fix(fam, q, k):
    """|Fix| (incl. e), #fixed involutions (excl. e) for conjugation of order k on fam(2,q); None if no such element."""
    p, e = pp(q)
    if p == k:                                     # unipotent: C = Z(Q) x U
        return (2 * q, 1) if fam == 'sl' and p != 2 else (q, 0)
    if k == 2: return None
    for t in (q - 1, q + 1):
        if t % k == 0:
            if fam == 'sl': return t, (1 if q % 2 else 0)
            if fam == 'psl': return (t // 2, 1 if (t // 2) % 2 == 0 else 0) if q % 2 else (t, 0)
            return t, (1 if t % 2 == 0 else 0)     # pgl: torus of order q -+ 1
    return None
def frob_fix(fam, q, k):
    p, e = pp(q)
    if e % k: return None
    q0 = p ** (e // k); F = order(fam, q0)
    inv = 1 if (fam == 'sl' and p != 2) else (q0 * q0 - 1 if p == 2 else (q0 * (q0 - 1) // 2 if fam == 'psl' and q0 % 4 == 1 else q0 * (q0 + 1) // 2 if fam == 'psl' else q0 * q0))
    return F, inv
w = W(d, D)
cands = []
for q in range(3, 2100):
    if not pp(q): continue
    for fam in fams:
        if fam == 'psl' and q % 2 == 0: continue
        if fam == 'pgl' and q % 2 == 0: continue   # pgl = sl in characteristic 2
        if fam == 'sl' and q % 2 == 0 and D % 2: continue
        o = order(fam, q)
        if o > hi // 2: continue
        for k in ks:
            syms = [('conj', conj_fix(fam, q, k))]
            if 'frob' in flags: syms.append(('frob', frob_fix(fam, q, k)))
            for sym, fx in syms:
                if fx is None: continue
                for n in range(1, min(int(opt['nmax']), int(opt['nq']) * q) + 1):
                    N = o * n
                    if 2 * N > hi: break
                    if 2 * N < lo: continue
                    if n > 1 and any(p % k != 1 for p in factor(n)): continue
                    lam = w / N; mu = N * math.exp(-lam)
                    fix, finv = fx                  # z -> r z fixes only z = 0
                    gen = fix - 1 - (finv if D % 2 else 0)
                    phi = gen * math.exp(-lam / k) + (2 * finv * math.exp(-lam / (2 * k)) if D % 2 else 0)
                    muA = (mu - fix * math.exp(-lam)) / k + phi
                    ev = 1e5 * math.exp((muA - 13) / 2)
                    secs = ev * float(opt['c']) * N
                    cands.append((2 * N, fam, q, n, k, sym, fix, mu, phi, muA, ev, secs))
H = float(opt['hours']) * 3600
print('# (%d,%d) lambda~%.1f, %d candidates; fits = predicted single-thread time <= %s h' % (d, D, w / (lo / 2), len(cands), opt['hours']))
print('%12s %-6s %5s %5s k %-4s %5s %6s %5s %6s %9s %8s' % ('vertices', 'fam', 'q', 'n', 'sym', 'fix', 'mu', 'phi', 'mu_A', 'evals', 'hours'))
rows = sorted(cands, key=lambda r: -r[0]) if 'all' in flags else sorted([r for r in cands if r[11] <= H], key=lambda r: -r[0])
for r in rows[:int(opt['top'])]:
    print('%12d %-6s %5d %5d %d %-4s %5d %6.1f %5.2f %6.2f %9.2g %8.2f' % (r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10], r[11] / 3600))
