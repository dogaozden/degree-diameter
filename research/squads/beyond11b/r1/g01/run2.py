import sys, os, subprocess, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
import numpy as np, groups
from prod_specs import SPECS
D = int(sys.argv[1]); lo, hi = int(sys.argv[2]), int(sys.argv[3]); budget = float(sys.argv[4])
LOG = f'/home/user/degree-diameter/research/squads/beyond11b/r1/g01/prod_D{D}.log'
t0 = time.time()
R = '/home/user/degree-diameter/research/squads/beyond11b/r1/g01/'
for spec in SPECS:
    if time.time() - t0 > budget: break
    T = groups.table(spec); n = len(T)
    if n < lo or n > hi: continue
    ts = time.time()
    fn = R + 't_prod.bin'
    with open(fn, 'wb') as f:
        np.array([n], dtype=np.int32).tofile(f); T.astype(np.uint16).tofile(f)
    pref = R + 'hit_prod_D%d_' % D + spec.replace(' ', '_')
    out = subprocess.run(['timeout', '100', 'nice', '-n', '10', '/home/user/degree-diameter/research/squads/beyond11b/bin/exh3', fn, str(D), pref],
                         capture_output=True, text=True).stdout
    g = [l for l in out.splitlines() if l.startswith('GROUP')]
    r = [l for l in out.splitlines() if l.startswith('RESULT')]
    line = f"{spec} | N={n} 2N={2*n} | {g[0] if g else 'NORUN ' + out[-100:]} | {r[0] if r else ''} | {time.time()-ts:.1f}s"
    with open(LOG, 'a') as f: f.write(line + '\n')
    os.remove(fn)
