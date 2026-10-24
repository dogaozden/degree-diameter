"""c6: H(q) + 4 fixed random matchings, zero hexagon voltages, CONSTANT extra shifts s_j per matching.
Walk voltage then depends only on the signed usage counts of each matching. Random search over s in Z_m^4.
Usage: python3 const_scan.py q m trials seed out_best.txt"""
import sys, subprocess, re
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/r1_d14D8/c6')
from mk_c6 import build
from hexlib import write_base
S = '/home/user/degree-diameter/research/squads/cells/d14D8_work/liftevalw'
q, m, trials, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
rng = np.random.default_rng(seed + 1000)
N, LP, PL, E0, Ms = build(q, m, seed, 4, 0)
hv = np.zeros((N, q + 1), dtype=np.int64)
best = None
def cost_for(s, fn):
    extra = [np.full(N, s[j], dtype=np.int64) for j in range(4)]
    _, _, _, E, _ = build(q, m, seed, 4, 0, extra_volt=extra, matchings=Ms)
    write_base(fn, N, m, E)
    r = subprocess.run([S, fn, '8', 'r:20:1'], capture_output=True, text=True)
    mm = re.search(r'COST (\d+)', r.stdout)
    return int(mm.group(1))
res = []
for t in range(trials):
    s = [int(x) for x in rng.integers(1, m, 4)]
    fn = out + '.tmp'
    c = cost_for(s, fn)
    res.append((c, s))
    if best is None or c < best[0]:
        best = (c, s)
        print('trial', t, 'best cost', c, 's', s, flush=True)
    if c == 0:
        break
print('FINAL m', m, 'best', best, flush=True)
