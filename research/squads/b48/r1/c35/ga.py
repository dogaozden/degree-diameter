# Genetic search over S = {0, x, y, z} for metacyclic Haar graphs (dipole4 lift), fitness = lift eval cost.
import random, subprocess, sys, time, json
T = '/home/user/degree-diameter/research/squads/b48/tools'
BASE = T + '/bases/dipole4.txt'
group = sys.argv[1]; budget = int(sys.argv[2]); seed = int(sys.argv[3])
MAXT = float(sys.argv[4]) if len(sys.argv) > 4 else 50.0
m, k, r = [int(v) for v in group.split(':')[1:]]
N = m * k
rng = random.Random(seed)
evals = 0
t0 = time.time()

def cost_batch(cands):
    global evals
    evals += len(cands)
    lines = ''.join('0 %d %d %d\n' % c for c in cands)
    out = subprocess.run([T + '/lift', BASE, group, '4', '8', 'eval'], input=lines, capture_output=True,
                         text=True, timeout=120).stdout.split('\n')
    res = []
    for i in range(len(cands)):
        s = out[i]
        res.append(10**9 if (s == 'invalid' or s == '') else int(s))
    return res

def idx(a, j):
    return (a % m) + m * (j % k)

def rand_el():
    return rng.randrange(1, N)

def local(e):  # small move on Z_m or Z_k part
    a, j = e % m, e // m
    if rng.random() < 0.5:
        a = (a + rng.choice([-3, -2, -1, 1, 2, 3])) % m
    else:
        j = (j + rng.choice([-1, 1])) % k
    return idx(a, j)

def valid(c):
    x, y, z = c
    return len({x, y, z}) == 3 and 0 not in (x, y, z)

def random_ind():
    while True:
        c = (rand_el(), rand_el(), rand_el())
        if valid(c):
            return c

def mutate(c):
    c = list(c)
    for i in range(3):
        if rng.random() < 0.3:
            c[i] = rand_el() if rng.random() < 0.4 else local(c[i])
    return tuple(c)

def crossover(p, q):
    # swap generators between parents: each slot taken from one parent at random
    return tuple(p[i] if rng.random() < 0.5 else q[i] for i in range(3))

P = 300; ELITE = 30
pop = [random_ind() for _ in range(P)]
fit = cost_batch(pop)
best = min(zip(fit, pop))
bestc, bestS = best
gen = 0; last_imp = 0; hist = []
while bestc > 0 and evals < budget and time.time() - t0 < MAXT:
    order = sorted(range(P), key=lambda i: fit[i])
    elite = [pop[i] for i in order[:ELITE]]
    kids = []
    while len(kids) < P - ELITE:
        # tournament selection of size 2
        a = min(rng.sample(range(P), 2), key=lambda i: fit[i])
        b = min(rng.sample(range(P), 2), key=lambda i: fit[i])
        c = mutate(crossover(pop[a], pop[b]))
        if valid(c):
            kids.append(c)
    kfit = cost_batch(kids)
    pop = elite + kids
    fit = [fit[order[i]] for i in range(ELITE)] + kfit
    gen += 1
    cb, cS = min(zip(fit, pop))
    if cb < bestc:
        bestc, bestS, last_imp = cb, cS, gen
    hist.append(bestc)
    if gen - last_imp > 150:  # stagnation: reseed population but keep best
        pop = [bestS] + [random_ind() for _ in range(P - 1)]
        fit = cost_batch(pop)
        last_imp = gen
print(json.dumps({'group': group, 'N': N, 'seed': seed, 'best': bestc, 'S': [0] + list(bestS),
                  'gens': gen, 'evals': evals, 'time': round(time.time() - t0, 1)}))
