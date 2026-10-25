"""c7: genetic algorithm with orbit-block crossover over tau-invariant voltage vectors (q=5, C=1, r=2 equivariant
bijections fixed per run). Genome = per point-orbit: 6 incidence voltages (one per slot of the orbit representative)
+ 2 matching voltages. Crossover copies whole point-orbit blocks from one parent. Score = bcd --cost (pairs at
distance > 8 over tau-orbit sources). Usage: ga.py M SEED POP GENS TIME_LIMIT_S"""
import sys, time, os
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/projects/bigcheck-dist/d8')
import hexspec as hs

M, SEED, POP, GENS, TLIM = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
OUT = '/home/user/degree-diameter/research/squads/bcd-d8-r1/c7'
H = hs.Hex('/tmp/bcdt/hex/hex_q5.bin', '/tmp/bcdt/hex/singer_q5.bin')
N, q, NO = H.N, H.q, len(H.prep)
rng = np.random.default_rng(SEED)
SIG = [hs.equivariant_bijection(H, rng) for _ in range(2)]
# fixed incidence structure: for each point p, the slot index s of each incident line (orbit-rep frame)
SLOT = np.zeros((N, q + 1), dtype=np.int64)   # SLOT[p, k] = (orbit-frame slot s) of k-th incident line of p
for p in range(N):
    o, e = H.porb[p], H.ppos[p]; r = H.prep[o]
    for k, L in enumerate(H.plines[p]):
        L0 = L
        for _ in range((H.KA - e) % H.KA): L0 = H.tl[L0]
        SLOT[p, k] = list(H.plines[r]).index(L0)

def write(genome, path):
    w, a = genome  # w: (NO, q+1), a: (2, NO)
    edges = []
    for p in range(N):
        o = H.porb[p]
        for k, L in enumerate(H.plines[p]):
            edges.append((p, N + int(L), int(w[o, SLOT[p, k]]) % M))
    for j in range(2):
        edges += [(p, N + int(SIG[j][p]), int(a[j, H.porb[p]]) % M) for p in range(N)]
    hs.write_spec(path, H, M, edges)

def evaluate(genome, tag):
    path = f'{OUT}/tmp_{SEED}.spec'
    write(genome, path)
    c = hs.bcd_cost(path, 8, 8, threads=1)
    os.remove(path)
    return c

def rand_genome():
    return (rng.integers(0, M, (NO, q + 1)), rng.integers(0, M, (2, NO)))

def crossover(g1, g2):
    w1, a1 = g1; w2, a2 = g2
    mask = rng.random(NO) < 0.5
    w = np.where(mask[:, None], w1, w2); a = np.where(mask[None, :], a1, a2)
    return (w.copy(), a.copy())

def mutate(g, rate=0.01):
    w, a = g[0].copy(), g[1].copy()
    for o in range(NO):
        if rng.random() < rate:
            w[o] = rng.integers(0, M, q + 1); a[:, o] = rng.integers(0, M, 2)
    return (w, a)

t0 = time.time()
pop = [rand_genome() for _ in range(POP)]
fit = [evaluate(g, i) for i, g in enumerate(pop)]
best_c = min(fit); best_g = pop[int(np.argmin(fit))]
print(f"gen 0 best {best_c} mean {np.mean(fit):.1f} t={time.time()-t0:.0f}s", flush=True)
def tourn(k=3):
    idx = rng.choice(POP, k, replace=False); return pop[min(idx, key=lambda i: fit[i])]
for gen in range(1, GENS + 1):
    if best_c == 0 or time.time() - t0 > TLIM: break
    order = np.argsort(fit)
    newpop = [pop[order[0]], pop[order[1]]]
    newfit = [fit[order[0]], fit[order[1]]]
    while len(newpop) < POP:
        child = mutate(crossover(tourn(), tourn()))
        newpop.append(child); newfit.append(evaluate(child, len(newpop)))
    pop, fit = newpop, newfit
    i = int(np.argmin(fit))
    if fit[i] < best_c:
        best_c, best_g = fit[i], pop[i]
    print(f"gen {gen} best {min(fit)} mean {np.mean(fit):.1f} overall_best {best_c} t={time.time()-t0:.0f}s", flush=True)
path = f'{OUT}/best_M{M}_s{SEED}.spec'
write(best_g, path)
print(f"FINAL M={M} cost={best_c} spec={path}", flush=True)
