#!/usr/bin/env python3
"""Sweep of coordinate-based designs (c3). Each design: build base file in runs/, score with lifteval.
usage: python3 sweep_c3.py q SAMPLE_K seeds ms configs out_log [all_if_sampled_zero]
  seeds: comma list; ms: comma list; configs: comma list of hexmode:kappa:phimode
  Prints one line per design: q m seed config sampleCOST [allCOST].
  sampled check = lifteval r:K:7 ; if its COST is 0 and all=1, the exact all-source check runs too."""
import subprocess, sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import mk_c3
from hexlib import write_base

HERE = os.path.dirname(os.path.abspath(__file__))
LIFT = '/home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval'
q = int(sys.argv[1]); K = int(sys.argv[2])
seeds = [int(x) for x in sys.argv[3].split(',')]
ms = [int(x) for x in sys.argv[4].split(',')]
configs = sys.argv[5].split(',')
log = open(sys.argv[6], 'a')
do_all = int(sys.argv[7]) if len(sys.argv) > 7 else 1
os.makedirs(os.path.join(HERE, 'runs'), exist_ok=True)


def cost(fn, spec):
    r = subprocess.run([LIFT, fn, '8', spec], capture_output=True, text=True, timeout=900)
    mm = re.search(r'COST (\d+)', r.stdout)
    return int(mm.group(1)) if mm else -1


for cfg in configs:
    hexmode, kappa, phimode = cfg.split(':')
    for m in ms:
        for seed in seeds:
            if hexmode == 'proj' and kappa == 'rand' and m < q + 1:
                continue
            N, E = mk_c3.build_edges(q, m, seed, hexmode, kappa, phimode)
            fn = os.path.join(HERE, 'runs', f'q{q}_{hexmode}_{kappa}_{phimode}_m{m}_s{seed}.txt')

            write_base(fn, N, m, E)
            c = cost(fn, f'r:{K}:7')
            line = f'q{q} m{m} seed{seed} {cfg} sample{K}_cost {c}'
            if c == 0 and do_all:
                ca = cost(fn, 'all')
                line += f' all_cost {ca}'
            print(line, flush=True)
            log.write(line + '\n'); log.flush()
