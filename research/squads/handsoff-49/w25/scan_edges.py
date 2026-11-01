# scan_edges.py: run tools/apsp (d=4 D=9) on every .edges file in the squad folders with n > 4970 (first token),
# resumable: results appended to scan_edges.tsv; stops after BUDGET seconds. Output: path, n, RESULT line.
import os, sys, time, subprocess
H = '/home/user/degree-diameter/research/squads/handsoff-49'
BUDGET = float(sys.argv[1]) if len(sys.argv) > 1 else 80
OUT = H + '/w25/scan_edges.tsv'
done = set()
if os.path.exists(OUT):
    done = {l.split('\t')[0] for l in open(OUT)}
files = []
for root, dirs, fs in os.walk(H):
    if root.startswith(H + '/w25'): continue
    for f in fs:
        if f.endswith('.edges'):
            files.append(os.path.join(root, f))
files.sort()
t0 = time.time(); n_new = 0
with open(OUT, 'a') as out:
    for p in files:
        if p in done: continue
        if time.time() - t0 > BUDGET: break
        try:
            with open(p) as fh:
                n = int(fh.readline().split()[0])
        except Exception:
            out.write('%s\t-\tnot an edge list\n' % p); n_new += 1; continue
        if n <= 4970 or n > 30000:
            out.write('%s\t%d\tskipped (n outside 4971..30000)\n' % (p, n)); n_new += 1; continue
        r = subprocess.run(['nice', '-n', '10', H + '/tools/apsp', p, '4', '9'], capture_output=True, text=True, timeout=60)
        line = [l for l in r.stdout.splitlines() if l.startswith('RESULT')]
        out.write('%s\t%d\t%s\n' % (p, n, line[-1] if line else 'no result')); n_new += 1
print('checked', n_new, 'files this run; total listed', len(files), 'elapsed %.0f s' % (time.time() - t0))
