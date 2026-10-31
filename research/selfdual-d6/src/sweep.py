#!/usr/bin/env python3
"""Run sdhi on a list of groups in parallel.  usage: sweep.py LIST K D OUTDIR NPAR
LIST: one group per line (sdhi factor specs, e.g. "pgl 5 cyc 14" or "meta 523 3 60"; text after '#' ignored).
Environment variables (ENUM, ECAP, SECS, ORDS, TYPES, ...) are passed to sdhi.  Each group gets OUTDIR/<name>.out;
OUTDIR/summary.txt gets one line per group: name N best-per-type sols secs.  Groups already in summary.txt are skipped.
Every SOL line is also appended to OUTDIR/SOLS.txt."""
import os, re, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
here = os.path.dirname(os.path.abspath(__file__))
lst, K, D, outdir, npar = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
os.makedirs(outdir, exist_ok=True)
summ = os.path.join(outdir, 'summary.txt')
done = set()
if os.path.exists(summ):
    for l in open(summ):
        done.add(l.split()[0])
groups = []
for l in open(lst):
    l = l.split('#')[0].strip()
    if l:
        groups.append(l)
def name(g): return '_'.join(g.split())
def run(g):
    nm = name(g)
    if nm in done or os.path.exists(os.path.join(outdir, 'STOP')):
        return
    out = os.path.join(outdir, nm + '.out')
    t0 = time.time()
    with open(out, 'w') as f:
        subprocess.run(['nice', '-n', '5', os.path.join(here, 'sdhi'), K, D] + g.split(), stdout=f, stderr=subprocess.STDOUT)
    txt = open(out).read()
    N = re.search(r' N (\d+)', txt); N = N.group(1) if N else '?'
    best = {}
    for m in re.finditer(r'^(?:TABU|ENUM) (psi\d+_t[\d+]+)\S* .*?best (-?\d+)', txt, re.M):
        b = int(m.group(2))
        if b >= 0: best[m.group(1)] = min(b, best.get(m.group(1), 1 << 30))
    sols = txt.count('\nSOL ')
    top = sorted(best.items(), key=lambda kv: kv[1])[:3]
    line = '%s N %s sols %d best %s secs %.0f\n' % (nm, N, sols, ' '.join('%s:%d' % kv for kv in top) or '-', time.time() - t0)
    with open(summ, 'a') as f: f.write(line)
    if sols:
        with open(os.path.join(outdir, 'SOLS.txt'), 'a') as f:
            for l in txt.splitlines():
                if l.startswith('SOL '): f.write(nm + ' ' + l + '\n')
with ThreadPoolExecutor(npar) as ex:
    list(ex.map(run, groups))
