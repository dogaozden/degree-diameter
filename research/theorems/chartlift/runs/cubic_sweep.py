"""Sweep cubic controllers (k=3) with a universal pencil-complete chart: cost 0 <=> diameter <= 5 and every vertex
on a 4-cycle.  Jobs: base (bases3/k3r*) x group (gtab/) with r*|G| in [LO, HI]; parallel workers."""
import subprocess, glob, os, sys, itertools
from concurrent.futures import ThreadPoolExecutor
LO, HI, SECS, WORKERS = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
here = os.path.dirname(os.path.abspath(__file__)) + '/..'
def order(p): return int(open(p).readline())
groups = sorted(glob.glob(here + '/gtab/*.txt'))
jobs = []
for base in sorted(glob.glob(here + '/bases3/k3r*.txt')):
    r = int(open(base).readline())
    for gp in groups:
        g = order(gp)
        if LO <= r * g <= HI: jobs.append((r * g, base, gp))
jobs.sort(reverse=True)
def run(job):
    m, base, gp = job; tag = os.path.basename(base)[:-4] + '__' + os.path.basename(gp)[:-4]
    out = subprocess.run([here + '/ctrl_search', base, gp, 'universal', str(SECS), '1', here + '/runs/cubic/' + tag],
                         capture_output=True, text=True).stdout.strip()
    return m, tag, out
os.makedirs(here + '/runs/cubic', exist_ok=True)
with ThreadPoolExecutor(WORKERS) as ex:
    for m, tag, out in ex.map(run, jobs):
        cost = out.split('best_cost=')[1].split()[0] if 'best_cost=' in out else '?'
        print('m=%d %s cost=%s' % (m, tag, cost), flush=True)
