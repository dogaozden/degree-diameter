"""sweep3.py (card c4): second matching p -- psi(p) with psi = delta o F (F = Frobenius collineation, frob9.npy)
or psi = delta^-1 o F. Layout as sweep2 (explicit sigma lists). Usage: python3 sweep3.py SPEC CONFIGS.json OUT.jsonl
Config: [m, psi_name, sigma1, sigma2]; psi_name in {'dF', 'dinvF', 'dFinv'}."""
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
F = np.load('/home/user/degree-diameter/research/squads/r2_d8c/c4/frob9.npy')
Pinv = perm_power(phi, -1)
psis = {'dF': phi[F[np.arange(N)]], 'dinvF': Pinv[F[np.arange(N)]], 'dFinv': phi[np.argsort(F)]}
for i, cfg in enumerate(configs):
    m, name, s1l, s2l = cfg
    psi = psis[name]
    assert all(psi[p] >= N for p in range(N)), 'psi must map points to lines'
    f1 = np.array(s1l)[c] % m
    f2 = np.array(s2l)[c] % m
    fn = os.path.join(WORK, f'y_{i}_m{m}.txt')
    with open(fn, 'w') as fh:
        fh.write(f'Z {m}\n{2 * N}\n' + ' '.join(['0'] * N + ['1'] * N) + '\n' + hp)
        fh.write('\n'.join(f'{p} {phi[p]} {f1[p]}' for p in range(N)) + '\n')
        fh.write('\n'.join(f'{p} {psi[p]} {f2[p]}' for p in range(N)) + '\n')
    r = subprocess.run(['timeout', '900', 'nice', '-n', '10', GLIFT, fn, spec], capture_output=True, text=True,
                       env=dict(os.environ, OMP_NUM_THREADS='1'))
    cost = None
    for line in r.stdout.splitlines():
        if line.startswith('COST'):
            cost = int(line.split()[1])
    out.write(json.dumps({'cfg': [m, name, s1l, s2l], 'spec': spec, 'cost': cost}) + '\n'); out.flush()
    print(i, m, name, cost, flush=True)
    os.remove(fn)
