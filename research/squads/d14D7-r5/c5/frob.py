"""Family F: Frobenius-type groups <x_beta(1), D> with D a split-torus element (x_beta normalised by D)."""
import sys, os, random, json, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lie
from lie import L, q, POS_ROOTS
os.makedirs('/home/user/degree-diameter/research/squads/d14D7-r5/c5/gens', exist_ok=True)
os.makedirs('/home/user/degree-diameter/research/squads/d14D7-r5/c5/sets', exist_ok=True)
LOG = '/home/user/degree-diameter/research/squads/d14D7-r5/c5/runs.jsonl'

def chi(beta, D):  # character of the torus on U_beta (up to inversion), D = (a,b,c,s)
    a, b, c = D[0], D[1], D[2]
    return pow(a, beta[0] % 10, q) * pow(b, beta[1] % 10, q) * pow(c, beta[2] % 10, q) % q

def ordmod(x):
    o = 1; y = x % q
    while y != 1: y = y * x % q; o += 1
    return o

def name_of(beta, D):
    return 'F_%s_%s' % ('.'.join(str(x + 1 if False else x) for x in beta), '-'.join(map(str, D)))

def run_group(name, mats, t=10, seed=1, keep=False):
    gp = os.path.join(lie.MYDIR, 'gens', name + '.txt')
    lie.write_gens(gp, mats, name)
    op = os.path.join(lie.MYDIR, 'sets', name + '.txt') if keep else None
    t0 = time.time()
    res, info = lie.run_orbclq(gp, t=t, seed=seed, out=op)
    best = lie.best_of(res)
    rec = {'name': name, 'best': best, 'res': res, 'secs': round(time.time() - t0, 1), 'info': info}
    with open(LOG, 'a') as f: f.write(json.dumps(rec) + '\n')
    return best, res, info

if __name__ == '__main__':
    random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
    nper = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    t = float(sys.argv[3]) if len(sys.argv) > 3 else 10
    seen = set()
    for beta in POS_ROOTS:
        xb = lie.root_elt(beta, 1)
        cnt = 0; tries = 0
        while cnt < nper and tries < 400:
            tries += 1
            a, b, c = (random.randrange(1, q) for _ in range(3)); s = random.choice([1, -1 % q])
            D = (a, b, c, s)
            k = ordmod(chi(beta, D))
            if k == 1: continue
            M = lie.torus(a, b, c, s)
            gsz = lie.group_size([xb, M], limit=3000)
            if gsz is None or not (22 <= gsz <= 1500): continue
            key = (beta, gsz, k)
            # cheap dedupe: same beta, same group order and same character order
            if (beta, gsz, k, tuple(sorted(D[:3]))) in seen: continue
            seen.add((beta, gsz, k, tuple(sorted(D[:3]))))
            cnt += 1
            name = 'F_%d%d%d_%s_%d_%d' % (beta[0] + 1, beta[1] + 1, beta[2] + 1, '-'.join(map(str, D)), gsz, k)
            name = name.replace('-1', 'm1').replace('+', 'p')
            best, res, info = run_group(name, [xb, M], t=t)
            print(name, 'order', gsz, 'chi-order', k, 'best', best, flush=True)
