"""c6 step 3: orbclq runs on subgroups S of Stab(R756) (order 2..12 conjugacy classes, from subgroups_2_12.json).
usage: runs.py CLASS_INDEX TSEC SEED [warm|scratch]
Writes runs/<name>.gens, runs/<name>.out (point set), runs/<name>.log (stdout/stderr) and prints the RESULT line."""
import os, sys, json, subprocess, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = os.path.join(HERE, 'runs')
os.makedirs(RUNS, exist_ok=True)
classes = json.load(open(os.path.join(HERE, 'subgroups_2_12.json')))
ci, tsec, seed, mode = int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
cl = classes[ci]
name = f"c{ci}_ord{cl['order']}_gens{'-'.join(map(str, cl['gen_orders']))}_{mode}_t{int(tsec)}_s{seed}"
gens_path = os.path.join(RUNS, f"c{ci}_ord{cl['order']}_gens{'-'.join(map(str, cl['gen_orders']))}.gens")
L.write_gens(gens_path, cl['gens'],
             comment=f"subgroup of Stab(R756) in N(<h>): order {cl['order']}, gen orders {cl['gen_orders']}")
out = os.path.join(RUNS, name + '.out')
cmd = [os.path.join(OVOID, 'orbclq'), gens_path, '-t', str(tsec), '-s', str(seed), '-o', out, '-v']
if mode == 'warm':
    cmd += ['-w', R756_PATH]
t0 = time.time()
p = subprocess.run(['timeout', '900', 'nice', '-n', '10'] + cmd, capture_output=True, text=True)
log = os.path.join(RUNS, name + '.log')
with open(log, 'w') as f:
    f.write(p.stdout + '\n--- stderr ---\n' + p.stderr)
res = [l for l in p.stdout.splitlines() if l.startswith('RESULT')]
print(name, 'exit', p.returncode, 'wall %.0fs' % (time.time() - t0))
print('  ' + (res[0] if res else p.stdout[-300:] + p.stderr[-300:]))
if os.path.exists(out):
    print('  checkset:', subprocess.run([sys.executable, os.path.join(OVOID, 'checkset.py'), out],
                                       capture_output=True, text=True).stdout.strip())
