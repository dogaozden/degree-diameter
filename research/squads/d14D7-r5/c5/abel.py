"""Family A: abelian groups <x_beta(1)> x <D> with D a split-torus element centralising x_beta (chi_beta(D) = 1)."""
import sys, os, random, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lie
from lie import L, q, POS_ROOTS
from frob import run_group, chi, ordmod
t = float(sys.argv[1]) if len(sys.argv) > 1 else 15
seed = int(sys.argv[2]) if len(sys.argv) > 2 else 3
nper = int(sys.argv[3]) if len(sys.argv) > 3 else 2
roots = sys.argv[4].split(',') if len(sys.argv) > 4 else None
random.seed(seed)
for beta in POS_ROOTS:
    tag = '%d%d%d' % (beta[0]+1, beta[1]+1, beta[2]+1)
    if roots and tag not in roots: continue
    xb = lie.root_elt(beta, 1)
    done = 0; tries = 0; seen = set()
    while done < nper and tries < 2000:
        tries += 1
        a, b, c = (random.randrange(1, q) for _ in range(3)); s = random.choice([1, q - 1])
        D = (a, b, c, s)
        if chi(beta, D) != 1: continue
        Mt = lie.torus(a, b, c, s)
        k = lie.mat_order_proj(Mt)
        if k in (None, 1, 11): continue
        gsz = lie.group_size([xb, Mt], limit=3000)
        if gsz is None or not (22 <= gsz <= 1500): continue
        if (gsz, k) in seen: continue
        seen.add((gsz, k)); done += 1
        name = 'A_%s_%d_%d_%d' % (tag, a, b * 100 + c * 10 + (s % q), gsz)
        best, res, info = run_group(name, [xb, Mt], t=t, seed=1)
        print(name, 'order', gsz, 'D-order', k, 'best', best, '|', ' '.join(i.strip() for i in info if 'good' in i or 'sizes' in i)[:300], flush=True)
