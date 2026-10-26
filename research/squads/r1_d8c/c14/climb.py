# Hill climb on the voltages of the GQ(5,5)-base lift (all 1248 edges voltage in Z_m), exact cost from liftevalw.
# Usage: python3 climb.py m_start m_step time_budget_s seed
import sys, random, subprocess, time, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
T = '/home/user/degree-diameter/research/squads/cells/d10D8_work/liftevalw'
D = os.path.dirname(os.path.abspath(__file__))
m0, step, budget, seed = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
t_end = time.time() + budget
def base_edges(m):
    # same base as gq_base.py mode rnd with given seed: rebuild structure from gq_base output with voltages 0
    import subprocess
    out = subprocess.run(['python3', os.path.join(D, 'gq_base.py'), str(m), str(seed), 'rnd'], capture_output=True, text=True).stdout.split('\n')
    hdr = out[0].split()
    E = [tuple(map(int, l.split())) for l in out[1:] if l.strip()]
    return E
def write(m, E, path):
    with open(path, 'w') as f:
        f.write('156 156 %d\n' % m)
        for a, b, v in E:
            f.write('%d %d %d\n' % (a, b, v))
def cost(m, E, path):
    write(m, E, path)
    r = subprocess.run([T, path, '8', 'all'], capture_output=True, text=True, env=dict(os.environ, OMP_NUM_THREADS='1'))
    for line in r.stdout.split('\n'):
        if line.startswith('COST'):
            return int(line.split()[1])
    return 10**9
m = m0
best_m = 0
while time.time() < t_end:
    E = base_edges(m)
    tmp = os.path.join(D, 'work_%d.txt' % m)
    c = cost(m, E, tmp)
    it = 0
    while c > 0 and time.time() < t_end:
        it += 1
        i = rng.randrange(len(E))
        a, b, v = E[i]
        nv = rng.randrange(m)
        E2 = E[:]; E2[i] = (a, b, nv)
        c2 = cost(m, E2, tmp)
        if c2 <= c:
            E, c = E2, c2
        if it % 200 == 0:
            print('m', m, 'iter', it, 'cost', c, flush=True)
    print('m', m, 'final cost', c, 'iters', it, flush=True)
    if c == 0:
        best_m = m
        write(m, E, os.path.join(D, 'best_m%d.txt' % m))
        m += step
    else:
        break
print('BEST_M', best_m, 'vertices', best_m * 312, 'copies_of_I(H5)', round(best_m * 312 / 7812, 2), flush=True)
