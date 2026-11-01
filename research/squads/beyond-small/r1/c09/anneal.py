# SA over flag voltages nu in {0,1} (flag voltage 4*nu) of the Z8 lift of W(q); cost = unordered far pairs (dist > 5).
# usage: anneal.py q mode(inv|free) sigma(polar|randN) iters seed tag
import random, sys, math, subprocess, json, time
from lift import make, setup
q = int(sys.argv[1]); mode = sys.argv[2]; sigsrc = sys.argv[3]; iters = int(sys.argv[4]); seed = int(sys.argv[5]); tag = sys.argv[6]
rng = random.Random(seed)
G = setup(q); N = G['N']
flags = [(p, lv) for p in range(N) for lv in G['pl_v'][p]]
if sigsrc == 'polar':
    phi = list(map(int, open('polarity_q%d.txt' % q).read().split()))
    sigma = [phi[p] for p in range(N)]
else:
    r = random.Random(int(sigsrc[4:]))
    sigma = [N + x for x in r.sample(range(N), N)]     # random bijection points -> lines
if mode == 'inv':
    assert sigsrc == 'polar'
    seen = set(); orbits = []
    for f in flags:
        if f in seen: continue
        p, lv = f; g = (phi[lv], phi[p])
        seen.add(f); seen.add(g); orbits.append([f] if g == f else [f, g])
else:
    orbits = [[f] for f in flags]
nu = {}
val = [rng.randint(0, 1) for _ in orbits]
for o, v in zip(orbits, val):
    for f in o: nu[f] = v
def cost(nu_):
    fn = f'/home/user/degree-diameter/research/squads/beyond-small/r1/c09/tmp_{tag}.edges'
    make(G, sigma, nu_, fn)
    out = subprocess.run(['./far', fn, '5', '8'], capture_output=True, text=True).stdout
    return int(out.split('far_unordered=')[1].split()[0])
cur = cost(nu); best = cur; bestnu = dict(nu); t0 = time.time()
T0, T1 = 30.0, 0.3
for it in range(iters):
    T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
    k = rng.randrange(len(orbits)); o = orbits[k]
    for f in o: nu[f] ^= 1
    c = cost(nu)
    if c <= cur or rng.random() < math.exp(-(c - cur) / T):
        cur = c
        if c < best:
            best = c; bestnu = dict(nu)
    else:
        for f in o: nu[f] ^= 1
    if it % 50 == 0:
        print('it', it, 'cur', cur, 'best', best, 'T', round(T, 2), 't', round(time.time() - t0), flush=True)
json.dump({'q': q, 'mode': mode, 'sigma': sigma, 'best': best,
           'nu': [[p, lv, bestnu[(p, lv)]] for (p, lv) in flags]}, open(f'best_{tag}.json', 'w'))
make(G, sigma, bestnu, f'best_{tag}.edges')
print('done best', best, flush=True)
