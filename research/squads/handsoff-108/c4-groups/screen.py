"""c4-groups screen: RANDORB=<samples> haar_sym2 on every candidate (k=3, m=3, f=1, ORBW=3), resumable.
usage: python3 screen.py candidates.tsv out.tsv SAMPLES [min_N,max_N|-] [spec-file|-] [FAMS env: comma list of families in order]
Appends: N fam spec mu fix min p1 p10 median secs status"""
import sys, os, re, subprocess, math, time
cand, out, samples = sys.argv[1], sys.argv[2], int(sys.argv[3])
BIN = '/home/user/degree-diameter/research/d10D8/sym2/haar_sym2'
W = 5380840  # Wwords(10,8) (D even: 10 * sum_{i<4} 9^(2i))
done = set()
if os.path.exists(out):
    for line in open(out):
        f = line.rstrip('\n').split('\t')
        if len(f) > 2: done.add(f[2])
todo = []
want = None
if len(sys.argv) > 5 and sys.argv[5] != '-':
    want = set(l.rstrip('\n') for l in open(sys.argv[5]) if l.strip())
FAMS = os.environ.get('FAMS', 'sl,pgl,psl,prod,agl1,meta').split(',')
for line in open(cand):
    N, fam, spec = line.rstrip('\n').split('\t')
    if want is not None and spec not in want: continue
    if spec in done: continue
    todo.append((int(N), fam, spec))
if len(sys.argv) > 4 and sys.argv[4] != '-':
    lo, hi = map(int, sys.argv[4].split(','))
    todo = [t for t in todo if lo <= t[0] <= hi]
todo.sort(key=lambda t: ((0 if int(t[2].split()[-1]) <= 500 else 1 if int(t[2].split()[-1]) <= 5000 else 2), FAMS.index(t[1].split(':')[0]) if t[1].split(':')[0] in FAMS else 99, t[0]))
todo = [t for t in todo if t[1].split(':')[0] in FAMS]
for N, fam, spec in todo:
    mu = N * math.exp(-W / N)
    env = dict(os.environ, ORBIT='3 3 1', RANDORB=str(samples), ORBW='3', THREADS='1')
    t0 = time.time()
    try:
        r = subprocess.run(['nice', '-n', '10', 'timeout', '120', BIN, '10', '8', '1', '108501', '8', '/dev/null'] + spec.split(),
                           env=env, capture_output=True, text=True)
        txt = r.stdout
    except Exception as e:
        txt = ''
    m = re.search(r'fix=(\d+) samples=\d+ min=(\d+) p1=(\d+) p10=(\d+) median=(\d+)', txt)
    dt = time.time() - t0
    if m:
        fix, mn, p1, p10, med = map(int, m.groups()); st = 'ok'
    else:
        fix = mn = p1 = p10 = med = -1
        err = (r.stderr.strip().splitlines() or ['no output'])[-1][:120] if txt == '' or True else ''
        st = 'fail:' + err.replace('\t', ' ')
    with open(out, 'a') as fo:
        fo.write('\t'.join(map(str, [N, fam, spec, '%.2f' % mu, fix, mn, p1, p10, med, '%.1f' % dt, st])) + '\n')
