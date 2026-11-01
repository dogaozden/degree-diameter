import sys, os, subprocess, time, json
sys.path.insert(0, '/home/user/degree-diameter/research/squads/beyond11b/tools')
import numpy as np, groups
from specs import specs
D = int(sys.argv[1]); lo, hi = int(sys.argv[2]), int(sys.argv[3]); budget = float(sys.argv[4])
LOG = f'/home/user/degree-diameter/research/squads/beyond11b/r1/g01/sweep_D{D}.log'
done = set()
if os.path.exists(LOG):
    for l in open(LOG):
        done.add(l.split('|')[0].strip())
t0 = time.time()
for N, spec in specs(D, lo, hi):
    if spec in done: continue
    if time.time() - t0 > budget: break
    ts = time.time()
    T = groups.table(spec)
    n = len(T)
    fn = f'/home/user/degree-diameter/research/squads/beyond11b/r1/g01/t.bin'
    with open(fn, 'wb') as f:
        np.array([n], dtype=np.int32).tofile(f); T.astype(np.uint16).tofile(f)
    pref = f'/home/user/degree-diameter/research/squads/beyond11b/r1/g01/hit_D{D}_' + spec.replace(' ', '_')
    out = subprocess.run(['timeout', '100', 'nice', '-n', '10', '/home/user/degree-diameter/research/squads/beyond11b/bin/exh3', fn, str(D), pref],
                         capture_output=True, text=True, env={**os.environ, 'OMP_NUM_THREADS': '1'}).stdout
    g = [l for l in out.splitlines() if l.startswith('GROUP')]
    r = [l for l in out.splitlines() if l.startswith('RESULT')]
    line = f"{spec} | N={n} 2N={2*n} | {g[0] if g else 'NORUN '+out[-100:]} | {r[0] if r else ''} | {time.time()-ts:.1f}s"
    with open(LOG, 'a') as f: f.write(line + '\n')
    print(line, flush=True)
    if os.path.exists(fn): os.remove(fn)
