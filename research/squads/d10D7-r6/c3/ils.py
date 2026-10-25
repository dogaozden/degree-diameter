#!/usr/bin/env python3
# c3 (squad round 6): iterated local search with LARGE kicks from a partial ovoid of H(8).
# kick kinds (fraction f of the current set S is removed, then pov2 regrows the rest from the kicked set):
#   random  : f*|S| uniformly random points of S removed
#   class   : random non-set point p; S-points with B(x,p) in a random union of GF(8) classes removed
#             (class 0 = points perpendicular to p, i.e. not opposite to p) until f*|S| removed
#   ball    : union of "not opposite to p" sets, S ∩ {x : B(x,p)=0}, over random non-set points p, until f*|S| removed
#   cross:TAG: half of S (random) plus points of another set (file TAG) added greedily while pairwise opposite
# usage: python3 ils.py loop CUR BEST LOG SECS BUDGET_S SEED0 PLAN   (PLAN e.g. random:0.10,class:0.25,cross:best134.txt)
import sys, os, random, json, subprocess, time, shutil
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import common as C
N = C.N
POV = os.path.join(HERE, 'pov3')
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
SETCHECK = '/home/user/degree-diameter/research/squads/d10D7-r4/tools/setcheck'

def read_ids(path):
    return [int(x) for x in open(path).read().split()]

def write_ids(path, ids):
    with open(path, 'w') as f:
        for x in ids:
            f.write('%d\n' % int(x))

def bvals(S, p):
    return C.Bval(C.V[np.asarray(S, dtype=np.int64)], C.V[p])

def kick(S, kind, frac, rng, pool_other=None):
    S = list(S); m = len(S); target = max(1, int(round(frac * m))); Sset = set(S)
    meta = {'kind': kind, 'frac': frac, 'S_size': m}
    if kind == 'random':
        rem = set(rng.sample(range(m), target))
    elif kind == 'class':
        while True:
            p = rng.randrange(N)
            if p not in Sset: break
        b = bvals(S, p)
        classes = list(range(8)); rng.shuffle(classes)
        rem = set(); T = []
        for c in classes:
            if len(rem) >= target: break
            T.append(c); rem |= set(np.nonzero(b == c)[0].tolist())
        meta.update({'p': p, 'T': T})
    elif kind == 'ball':
        rem = set(); ps = []
        while len(rem) < target:
            p = rng.randrange(N)
            if p in Sset: continue
            ps.append(p); rem |= set(np.nonzero(bvals(S, p) == 0)[0].tolist())
        meta.update({'ps': ps})
    else:
        raise ValueError(kind)
    keep = [S[i] for i in range(m) if i not in rem]
    meta['removed'] = len(rem); meta['init_size'] = len(keep); meta['forb'] = sorted(S[i] for i in rem)
    return keep, meta

def cross(S, other, rng):
    S = list(S); half = rng.sample(S, len(S) // 2); chosen = list(half); hs = set(chosen)
    cand = [x for x in other if x not in hs]; rng.shuffle(cand)
    for c in cand:
        if len(chosen) == 0 or np.all(bvals(chosen, c) != 0):
            chosen.append(c)
    meta = {'kind': 'cross', 'half': len(half), 'other_size': len(other), 'init_size': len(chosen),
            'forb': [x for x in S if x not in hs]}
    return chosen, meta

def check(path):
    r = subprocess.run([SETCHECK, HEX, path, 'points', 'opposite'], capture_output=True, text=True)
    return r.stdout.strip()

def loop(cur_p, best_p, log_p, secs, budget, seed0, plan):
    t_start = time.time(); it = 0
    rng = random.Random(seed0 * 7919 + 17)
    cur = read_ids(cur_p); best_size = len(read_ids(best_p))
    while time.time() - t_start < budget:
        spec = plan[it % len(plan)]
        kind, _, arg = spec.partition(':')
        seed = seed0 + it
        if kind == 'cross':
            other = read_ids(os.path.join(HERE, arg)) if os.path.exists(os.path.join(HERE, arg)) else read_ids(arg)
            init, meta = cross(cur, other, rng)
        else:
            init, meta = kick(cur, kind, float(arg), rng)
        ip = os.path.join(HERE, 'runs', 'it%03d_init.txt' % it)
        op = os.path.join(HERE, 'runs', 'it%03d_out.txt' % it)
        ep = os.path.join(HERE, 'runs', 'it%03d_err.txt' % it)
        write_ids(ip, init)
        fp = ip.replace('_init', '_forb'); forb = meta.pop('forb'); write_ids(fp, forb); meta['n_forb'] = len(forb)
        t0 = time.time()
        with open(ep, 'w') as ef:
            subprocess.run(['timeout', '150', 'nice', '-n', '10', POV, HEX, str(seed), str(secs), op,
                            '7', '10', '200000', '5', '1000000000000', '0', ip, fp, os.environ.get('FORB_ITERS', '1000000000000')],
                           stdout=subprocess.DEVNULL, stderr=ef)
        wall = time.time() - t0
        out = read_ids(op) if os.path.exists(op) else []
        chk = check(op) if out else 'NO OUTPUT'
        valid = chk.startswith('VALID')
        t_best = None
        for line in open(ep):
            if 'NEW BEST' in line and ('BEST %d ' % len(out)) in line:
                t_best = float(line.split('t=')[1].split('s')[0])
                break
        accepted = valid and len(out) >= len(cur)
        if accepted:
            cur = out; shutil.copy(op, cur_p)
        if valid and len(out) > best_size:
            best_size = len(out); shutil.copy(op, best_p)
        rec = dict(it=it, seed=seed, spec=spec, **meta, out_size=len(out), valid=valid, accepted=accepted,
                   cur_size=len(cur), best_size=best_size, t_reach_out=t_best, wall=round(wall, 1))
        with open(log_p, 'a') as lf:
            lf.write(json.dumps(rec) + '\n')
        print(json.dumps(rec), flush=True)
        it += 1
    return cur, best_size

if __name__ == '__main__':
    if sys.argv[1] == 'loop':
        cur_p, best_p, log_p = sys.argv[2], sys.argv[3], sys.argv[4]
        secs, budget, seed0 = int(sys.argv[5]), float(sys.argv[6]), int(sys.argv[7])
        plan = sys.argv[8].split(',')
        loop(cur_p, best_p, log_p, secs, budget, seed0, plan)
