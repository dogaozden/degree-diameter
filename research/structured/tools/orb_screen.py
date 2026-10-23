"""Screen groups for symmetric (orbit) search.
usage: python3 orb_screen.py d D LO HI "k m f" [--samples 1000] [--bin PATH] [--fams sl,psl,pgl,prod] [--anyn] [--top 20] [--list]
Lists G = Q x Z_n with LO <= |G| <= HI (Q = SL/PSL/PGL(2,q), or a product of two with a small first factor), keeps n
whose prime factors are all 1 mod k (so z -> r z has only the fixed point 0) unless --anyn, runs
'ORBIT="k m f" RANDORB=samples haar_sym ...' on each and prints them ranked by (p1 + p10)/2 of the cost, with mu and
|Fix(alpha)|.  Lines: rank, N, mu, fix, min, p1, p10, median, spec.  --list: only list the candidates with mu (for
groups too large to screen).  --save DIR: a sample of cost 0 is kept (haar_sym checks it and writes it) as
DIR/<tag>.txt with its log DIR/<tag>.log (orbq.sh names, seed tag "rand") and build_haar2.py's verdict."""
import sys, os, math, subprocess, re
args = sys.argv[1:]
d, D, lo, hi = int(args[0]), int(args[1]), int(args[2]), int(args[3]); kmf = args[4]
opt = {'samples': '1000', 'bin': os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'haar_sym'), 'fams': 'sl,psl,pgl,prod', 'top': '30', 'nmax': '400'}
flags = set()
i = 5
while i < len(args):
    if args[i] in ('--anyn', '--list'): flags.add(args[i][2:]); i += 1
    else: opt[args[i][2:]] = args[i + 1]; i += 2
k = int(kmf.split()[0])
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
pp = lambda q: len(factor(q)) == 1
fams = opt['fams'].split(',')
base = []
for q in range(3, 1300):
    if not pp(q): continue
    o = q * (q * q - 1)
    if o <= hi:
        if 'sl' in fams: base.append(('sl %d' % q, o))
        if 'pgl' in fams: base.append(('pgl %d' % q, o))
    if q % 2 and o // 2 <= hi and 'psl' in fams: base.append(('psl %d' % q, o // 2))
prods = []
if 'prod' in fams:
    small = [(s, o) for s, o in base if o <= 2000 and not s.startswith('pgl')]
    for s1, o1 in small:
        for s2, o2 in base:
            if o1 * o2 <= hi and o2 >= o1 and not s2.startswith('pgl'): prods.append(('prod %s %s' % (s1, s2), o1 * o2))
cands = set()
for s, o in base + prods:
    for n in range(1, int(opt['nmax']) + 1):
        N = o * n
        if N > hi: break
        if N < lo: continue
        if 'anyn' not in flags and n > 1 and any(p % k != 1 for p in factor(n)): continue
        cands.add((N, '%s %d' % (s, n)))
w = W(d, D)
if 'list' in flags:
    for N, spec in sorted(cands): print('N=%d 2N=%d mu=%.1f  %s' % (N, 2 * N, N * math.exp(-w / N), spec))
    sys.exit(0)
rows = []
for N, spec in sorted(cands):
    mu = N * math.exp(-w / N)
    env = dict(os.environ, ORBIT=kmf, RANDORB=opt['samples'])
    out = '/dev/null'
    if 'save' in opt:
        kk, mm, ff = kmf.split()[:3]
        tag = 'd%dD%d_%s_orb%s%s_rand' % (d, D, spec.replace(' ', '_'), kk, 'f0' if ff == '0' else '')
        out = os.path.join(opt['save'], tag + '.txt')
    r = subprocess.run([opt['bin'], str(d), str(D), '1', '1', '8', out] + spec.split(), env=env, capture_output=True, text=True)
    if out != '/dev/null' and os.path.exists(out):
        chk = subprocess.run(['python3', os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'frontier', 'build_haar2.py'), out],
                             capture_output=True, text=True).stdout.strip().splitlines()[-3:] if N <= 10000000 else ['(no build_haar2 above 10M)']
        open(out[:-4] + '.log', 'w').write(r.stderr + r.stdout + '\n'.join(chk) + '\n')
        print('# SAVED %s: %s' % (out, chk[-1]), flush=True)
    m = re.search(r'fix=(\d+) samples=\d+ min=(\d+) p1=(\d+) p10=(\d+) median=(\d+)', r.stdout)
    if not m: print('#', spec, 'failed:', (r.stderr.strip().splitlines() or [''])[-1], flush=True); continue
    fix, mn, p1, p10, med = map(int, m.groups())
    rows.append(((p1 + p10) / 2, N, mu, fix, mn, p1, p10, med, spec))
    print('# %-34s N=%d mu=%.1f fix=%d min=%d p1=%d p10=%d median=%d' % (spec, N, mu, fix, mn, p1, p10, med), flush=True)
rows.sort()
for i, r in enumerate(rows[:int(opt['top'])]):
    print('%2d N=%d mu=%.1f fix=%d min=%d p1=%d p10=%d median=%d  %s' % ((i + 1,) + r[1:]))
