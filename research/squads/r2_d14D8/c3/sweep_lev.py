"""Level-family sweep (c3): build_lev(q, k, seed, hexsub, colour, phi2) for k with gcd(5,k)=1; sampled + exact scoring.
usage: python3 sweep_lev.py q k seeds hexsubs colours phi2s K [all]"""
import sys, os, re, subprocess
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import mk_c3
from hexlib import write_base
LIFT = '/home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval'
q, k = int(sys.argv[1]), int(sys.argv[2])
seeds = [int(x) for x in sys.argv[3].split(',')]
hexsubs = sys.argv[4].split(','); colours = sys.argv[5].split(','); phi2s = sys.argv[6].split(',')
K = int(sys.argv[7]); do_all = int(sys.argv[8]) if len(sys.argv) > 8 else 0
os.makedirs(os.path.join(HERE, 'runs'), exist_ok=True)
def cost(fn, spec):
    r = subprocess.run([LIFT, fn, '8', spec], capture_output=True, text=True, timeout=900)
    mm = re.search(r'COST (\d+)', r.stdout); return int(mm.group(1)) if mm else -1
for hs in hexsubs:
  for co in colours:
    for p2 in phi2s:
      for s in seeds:
        m, N, E = mk_c3.build_lev(q, k, s, hs, co, p2)
        fn = os.path.join(HERE, 'runs', f'lev_q{q}_k{k}_{hs}_{co}_{p2}_s{s}.txt')
        write_base(fn, N, m, E)
        c = cost(fn, f'r:{K}:7'); line = f'LEV q{q} m{m} k{k} seed{s} hex={hs} colour={co} phi2={p2} sample{K}_cost {c}'
        if c == 0 and do_all: line += f' all_cost {cost(fn, "all")}'
        print(line, flush=True)
