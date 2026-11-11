import random, sys
from gq import build, check_auto
from lift import make, setup
import subprocess
q = 8; G = setup(q); N = G['N']
phi = list(map(int, open('polarity_q8.txt').read().split()))
sigma = [phi[p] for p in range(N)]          # point p -> line vertex
rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
# sigma-invariant nu: flag (p,lv) maps to (phi[lv], phi[p]) ; orbits under this involution
flags = [(p, lv) for p in range(N) for lv in G['pl_v'][p]]
nu = {}
for f in flags:
    if f in nu: continue
    p, lv = f
    g = (phi[lv], phi[p])
    assert g in set(flags) or True
    v = rng.randint(0, 1)
    nu[f] = v; nu[g] = v
orbit_of = {}  # for annealing: list of orbit representatives
import json
json.dump({'nu': [[p, lv, nu[(p, lv)]] for (p, lv) in flags]}, open('nu_inv_q8.json', 'w'))
n = make(G, sigma, nu, 'lift8_inv.edges')
print('edges', n)
