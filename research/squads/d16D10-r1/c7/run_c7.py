# c7 runner: alpha/orbit variants on sl 53 x Z91 (mu 18.25), an equal-mu p=1 mod 3 group (sl 19 x Z1981),
# and psl 157 x Z7 (mu 18.27). Eval-based annealing clock (VCLOCK=0.1 s per step, = the default 20 s COOL at
# ~8 evals/step unloaded), budget MAXSTEPS steps, so results do not depend on machine load. 2 runs at a time.
import os, subprocess, time, json, re, sys
from concurrent.futures import ThreadPoolExecutor
T = '/tmp/claude-0/-home-user-degree-diameter/4ce63409-b0f8-5c33-8f23-00173ad34031/scratchpad/tools/research/structured'
HERE = '/home/user/degree-diameter/research/squads/d16D10-r1/c7'
BIN = os.path.join(T, 'haar_sym')
MAXSTEPS = '600'
V1 = {'ORBIT': '3 5 1'}
V2 = {'ORBIT': '3 4 4'}
V3 = {'ORBIT': '3 5 1', 'ORBW': '3'}
V4 = {'ORBIT': '3 5 1', 'AR': '29'}
SL53 = ['sl', '53', '91']
SL19 = ['sl', '19', '1981']
PSL157 = ['psl', '157', '7']
JOBS = []
def add(tag, env, grp, seeds):
    for s in seeds: JOBS.append((f'{tag}_s{s}', env, grp, s))
ORDER = [('sl53_v1_351', V1, SL53, 1), ('sl53_v2_344', V2, SL53, 1), ('sl53_v3_orbw3', V3, SL53, 1),
         ('psl157_v1_351', V1, PSL157, 1), ('psl157_v2_344', V2, PSL157, 1), ('sl19_v1_351', V1, SL19, 1),
         ('sl53_v4_ar29', V4, SL53, 1), ('sl53_v1_351', V1, SL53, 2), ('sl53_v2_344', V2, SL53, 2),
         ('sl53_v3_orbw3', V3, SL53, 2), ('psl157_v1_351', V1, PSL157, 2), ('psl157_v2_344', V2, PSL157, 2),
         ('sl19_v1_351', V1, SL19, 2), ('sl53_v4_ar29', V4, SL53, 2), ('sl53_v1_351', V1, SL53, 3),
         ('sl53_v2_344', V2, SL53, 3), ('sl53_v3_orbw3', V3, SL53, 3), ('sl19_v1_351', V1, SL19, 3)]
JOBS = [(f'{t}_s{s}', env, grp, s) for (t, env, grp, s) in ORDER]
def run(job):
    tag, envx, grp, seed = job
    env = dict(os.environ); env.update(envx)
    env.update({'THREADS': '1', 'VCLOCK': '0.1', 'MAXSTEPS': MAXSTEPS})
    cmd = ['timeout', '300', 'nice', '-n', '10', BIN, '16', '8', '600', str(seed), '8', '/dev/null'] + grp
    t0 = time.time()
    p = subprocess.run(cmd, env=env, capture_output=True, text=True)
    wall = time.time() - t0
    open(os.path.join(HERE, 'logs', tag + '.out'), 'w').write(p.stdout)
    open(os.path.join(HERE, 'logs', tag + '.err'), 'w').write(p.stderr)
    res = [l for l in p.stdout.splitlines() if l.startswith('RESULT')]
    rec = {'tag': tag, 'env': envx, 'group': ' '.join(grp), 'seed': seed, 'rc': p.returncode, 'wall': round(wall, 1),
           'check': 'OK' if 'full diameter check: OK' in p.stdout else 'none'}
    m = re.search(r'best=(-?\d+) evals=(\d+) time=([\d.]+)', res[0]) if res else None
    if m: rec.update(best=int(m.group(1)), evals=int(m.group(2)), search_time=float(m.group(3)))
    else: rec.update(best=None, evals=None, error=p.stderr.strip().splitlines()[-1:] if p.stderr.strip() else '')
    with open(os.path.join(HERE, 'results.jsonl'), 'a') as f: f.write(json.dumps(rec) + '\n')
    print(json.dumps(rec), flush=True)
    return rec
if __name__ == '__main__':
    open(os.path.join(HERE, 'results.jsonl'), 'w').close()
    with ThreadPoolExecutor(max_workers=2) as ex:
        list(ex.map(run, JOBS))
    print('ALL DONE', flush=True)
