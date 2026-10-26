"""sweep2.py (card c4): explicit layouts. Config: [m, k, sigma1 (q+1 ints), sigma2 (q+1 ints), axis_seed].
f1(p) = sigma1[c(p)] mod m, f2(p) = sigma2[c(p)] mod m; matching 1 p--P(p), matching 2 p--P^k(p).
Usage: python3 sweep2.py SPEC CONFIGS.json OUT.jsonl"""
import sys, json, subprocess, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_c4 import setup, hexpart, perm_power
GLIFT = '/home/user/degree-diameter/research/squads/cells/d10D8_work/glift'
WORK = '/home/user/degree-diameter/research/squads/r2_d8c/c4/work'
PHI = '/home/user/degree-diameter/research/squads/r1_d8c/c5/dual9.phi'
q = 9
spec = sys.argv[1]
configs = json.load(open(sys.argv[2]))
out = open(sys.argv[3], 'a')
N, LP, phi, c = setup(q, PHI, 1)
hp = hexpart(N, LP)
for i, cfg in enumerate(configs):
    m, k, s1l, s2l = cfg[:4]
    f1 = (np.array(s1l)[c] % m)
    f2 = (np.array(s2l)[c] % m)
    Pk = perm_power(phi, k)
    fn = os.path.join(WORK, f'x_{i}_m{m}.txt')
    with open(fn, 'w') as fh:
        fh.write(f'Z {m}\n{2 * N}\n' + ' '.join(['0'] * N + ['1'] * N) + '\n' + hp)
        fh.write('\n'.join(f'{p} {phi[p]} {f1[p]}' for p in range(N)) + '\n')
        fh.write('\n'.join(f'{p} {Pk[p]} {f2[p]}' for p in range(N)) + '\n')
    r = subprocess.run(['timeout', '900', 'nice', '-n', '10', GLIFT, fn, spec], capture_output=True, text=True,
                       env=dict(os.environ, OMP_NUM_THREADS='1'))
    cost = None
    for line in r.stdout.splitlines():
        if line.startswith('COST'):
            cost = int(line.split()[1])
    out.write(json.dumps({'cfg': cfg, 'spec': spec, 'cost': cost}) + '\n'); out.flush()
    print(i, m, k, cost, flush=True)
    os.remove(fn)
