"""sweep.py: evaluate pencil-dual lifts (card c4). Usage:
  python3 sweep.py SRC SPEC CONFIGS.json OUT.jsonl
CONFIGS.json: list of [m, k, A1, s1, A2, s2, axis_seed]; SPEC like r:64:1 or all.
Prints one JSON line per config to OUT.jsonl (appends) with the glift COST."""
import sys, json, subprocess, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gen_c4 import setup, hexpart, write_base

GLIFT = '/home/user/degree-diameter/research/squads/cells/d10D8_work/glift'
WORK = '/home/user/degree-diameter/research/squads/r2_d8c/c4/work'
PHI = '/home/user/degree-diameter/research/squads/r1_d8c/c5/dual9.phi'
q = 9
spec = sys.argv[2]
configs = json.load(open(sys.argv[3]))
out = open(sys.argv[4], 'a')
cache = {}
for cfg in configs:
    m, k, A1, s1, A2, s2, aseed = cfg
    if aseed not in cache:
        cache = {aseed: setup(q, PHI, aseed)}
    N, LP, phi, c = cache[aseed]
    hp = hexpart(N, LP)
    tag = f'm{m}_k{k}_A{A1}_{s1}_A{A2}_{s2}_s{aseed}'
    fn = os.path.join(WORK, f'{tag}.txt')
    with open(fn, 'w') as fh:
        write_base(fh, N, m, hp, phi, c, k, A1, s1, A2, s2, q)
    r = subprocess.run(['timeout', '900', 'nice', '-n', '10', GLIFT, fn, spec],
                       capture_output=True, text=True, env=dict(os.environ, OMP_NUM_THREADS='1'))
    txt = r.stdout.strip().splitlines()
    cost = None
    for line in txt:
        if line.startswith('COST'):
            cost = int(line.split()[1])
    rec = {'cfg': cfg, 'spec': spec, 'cost': cost, 'tail': txt[-1] if txt else r.stderr[-200:]}
    out.write(json.dumps(rec) + '\n'); out.flush()
    print(tag, cost, flush=True)
    os.remove(fn)
