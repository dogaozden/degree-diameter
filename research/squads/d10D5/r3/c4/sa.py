"""Annealing over sigma (non-freed entries) for uncrowded random freed-flag sets; objective = coverage holes
of the core model (coset-1 points + dual coset-2 lines, routes (i),(ii),(i*),(ii*); NO hub routes)."""
import sys, time, math, random, json
sys.dont_write_bytecode = True
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D5/r3/c4')
import numpy as np
from cov import N, PM, LM, core

def holes(F, sig):
    res = core(F, sig, None)
    return sum(int(r['unc_p'].sum()) + int(r['unc_l'].sum()) for r in res), res

def random_uncrowded(k, rng):
    F, Ls = [], []
    pts = list(range(N)); rng.shuffle(pts)
    for p in pts:
        if len(F) == k: break
        if any(PM[p][f] for f in F): continue
        from cov import LOF
        cands = [l for l in LOF[p] if not any(LM[l][m] for m in Ls)]
        if not cands: continue
        F.append(p); Ls.append(rng.choice(cands))
    return F, Ls

def init_sigma(F, Ls, rng):
    fixed = dict(zip(F, Ls)); rest_pts = [x for x in range(N) if x not in fixed]
    rest_lines = [m for m in range(N) if m not in set(Ls)]; rng.shuffle(rest_lines)
    sig = [0] * N
    for p, l in fixed.items(): sig[p] = l
    for x, m in zip(rest_pts, rest_lines): sig[x] = m
    return sig

def anneal(F, sig, rng, seconds, T0=1.5, T1=0.05):
    nonF = [x for x in range(N) if x not in set(F)]
    cur, _ = holes(F, sig); best = cur; bestsig = list(sig)
    t0 = time.time(); it = 0
    while time.time() - t0 < seconds and best > 0:
        frac = (time.time() - t0) / seconds
        T = T0 * (T1 / T0) ** frac
        x, y = rng.sample(nonF, 2)
        sig[x], sig[y] = sig[y], sig[x]
        new, _ = holes(F, sig); d = new - cur
        if d <= 0 or rng.random() < math.exp(-d / T):
            cur = new
            if cur < best: best = cur; bestsig = list(sig)
        else:
            sig[x], sig[y] = sig[y], sig[x]
        it += 1
    return best, bestsig, it

if __name__ == '__main__':
    k = int(sys.argv[1]); seconds = float(sys.argv[2]); seed = int(sys.argv[3])
    rng = random.Random(seed)
    F, Ls = random_uncrowded(k, rng)
    print('k', len(F), 'uncrowded sample F', F, 'lines', Ls, flush=True)
    sig = init_sigma(F, Ls, rng)
    h0, _ = holes(F, sig)
    best, bestsig, it = anneal(F, sig, rng, seconds)
    _, res = holes(F, bestsig)
    per_p = [int(r['unc_p'].sum()) for r in res]; per_l = [int(r['unc_l'].sum()) for r in res]
    print(json.dumps(dict(k=len(F), seed=seed, start_holes=h0, best_holes=best, iters=it, per_point=per_p,
                          per_line=per_l, F=F, lines=Ls)), flush=True)
    json.dump(dict(F=F, lines=Ls, sigma=bestsig), open(f'/home/user/degree-diameter/research/squads/d10D5/r3/c4/sa_k{k}_s{seed}.json', 'w'))
