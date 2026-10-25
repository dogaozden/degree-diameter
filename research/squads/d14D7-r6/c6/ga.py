#!/usr/bin/env python3
"""c6: genetic recombination over mirrored-extension states (R = R756, see research/cell147/mirror/README.md).

A state is a list of pairs (x, L): x a point id, L a line id (hexagon ids). X pairwise opposite (B != 0), lines pairwise
opposite (distance 6), no line in S. F = k - cost with cost = sum over types of max(0, #base points - #usable spread
lines), the same formula as mirror_sa4.py / mirror_build.py.

Crossover: keep a random part of parent A's pairs, then add compatible pairs of parent B greedily (points opposite,
lines opposite). Screening: many children are scored without repair; the best distinct ones are repaired with
mirror_sa4.py --init (short annealing, one process at a time) and the repaired states go back into the population.
usage: ga.py --pop STATE.npz [...] --out DIR [--gens 2] [--children 400] [--repair 5] [--secs 40] [--seed 6]
       [--deadline UNIX_TIME]   (no new repair is started after the deadline)"""
import numpy as np, sys, os, time, argparse, subprocess, random
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
from hexmod import Hex
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
ap = argparse.ArgumentParser()
ap.add_argument('--pop', nargs='+', required=True); ap.add_argument('--out', required=True)
ap.add_argument('--gens', type=int, default=2); ap.add_argument('--children', type=int, default=400)
ap.add_argument('--repair', type=int, default=5); ap.add_argument('--secs', type=float, default=40)
ap.add_argument('--psize', type=int, default=8); ap.add_argument('--seed', type=int, default=6)
ap.add_argument('--deadline', type=float, default=0)
a = ap.parse_args(); os.makedirs(a.out, exist_ok=True)
rr = random.Random(a.seed); t0 = time.time()
logf = open(os.path.join(a.out, 'ga.log'), 'a')
def P(*s):
    msg = ' '.join(map(str, s)); print(msg, flush=True); logf.write(msg + '\n'); logf.flush()

H = Hex(SP + 'hex_q11.bin'); N = H.N
R = np.load(SP + 'R756idx.npy'); S = np.load(SP + 'S_herm.npy'); nS = len(S)
Sline = -np.ones(N, dtype=np.int64); Sline[H.lp[S].reshape(-1)] = np.repeat(np.arange(nS), H.lp.shape[1])
W = (1 << np.arange(62, dtype=np.int64))
LSc = {}
def lsv(l):
    """(spread lines at distance 4 from line l, spread lines concurrent with l) as bool vectors over S."""
    if l not in LSc:
        near = Sline[H.lp[H.pl[H.lp[l]]].reshape(-1)]; near = near[near >= 0]
        conc = Sline[H.lp[l]]; conc = conc[conc >= 0]
        v2 = np.zeros(nS, bool); v2[conc] = True
        v4 = np.zeros(nS, bool); v4[near] = True; v4 &= ~v2
        LSc[l] = (v4, v2)
    return LSc[l]

def score(pairs):
    xs = [p[0] for p in pairs]; ls = [p[1] for p in pairs]; k = len(xs)
    if k == 0: return 0
    NRm = (H.Bmat(np.array(xs), R) == 0)                 # k x 756: point x at distance 4 from base point
    tR = NRm.T.astype(np.int64) @ W[:k]
    V = [lsv(l) for l in ls]
    v4 = np.array([v[0] for v in V]); v2 = np.array([v[1] for v in V])
    ex = v2.any(axis=0)
    tS = v4.T.astype(np.int64) @ W[:k]
    ur, cr = np.unique(tR, return_counts=True)
    us, cs = np.unique(tS[~ex], return_counts=True)
    pos = np.searchsorted(us, ur); pos[pos >= len(us)] = 0
    have = np.where(us[pos] == ur, cs[pos], 0)
    return k - int(np.maximum(0, cr - have).sum())

def pts_ok(x, xs):
    return not xs or bool((H.Bmat(np.array([x]), np.array(xs)) != 0).all())

def lines_ok(l, ls):
    C = H.lp[H.pl[H.lp[l]]].reshape(-1)                  # points at distance <= 3 from l
    return not any(np.isin(H.lp[m], C).any() for m in ls)

def make_child(A, B):
    sa = rr.randint(max(1, len(A) // 2), len(A))
    child = rr.sample(A, sa)                             # compatible: a subset of parent A
    target = rr.randint(sa, sa + len(B) // 2 + 1)
    for x, l in rr.sample(B, len(B)):
        if len(child) >= target: break
        if any(x == c[0] for c in child) or any(l == c[1] for c in child): continue
        if not pts_ok(x, [c[0] for c in child]): continue
        if not lines_ok(l, [c[1] for c in child]): continue
        child.append((x, l))
    return child

def load_state(path):
    st = np.load(path)
    return [(int(x), int(l)) for x, l in zip(st['X'], st['L'])]

def key(pairs): return frozenset(pairs)

pop = {}
for p in a.pop:
    pr = load_state(p); pop[key(pr)] = (score(pr), pr)
P('init pop F:', sorted([v[0] for v in pop.values()], reverse=True), f'[{time.time()-t0:.0f}s]')
best = max(pop.values(), key=lambda v: v[0])
P('best init', best[0], 'k', len(best[1]))

def save_best(F, pairs, tag):
    np.savez(os.path.join(a.out, 'best_state.npz'), X=np.array([p[0] for p in pairs]), L=np.array([p[1] for p in pairs]), R=R)
    P(f'NEW BEST F={F} k={len(pairs)} ({tag}) [{time.time()-t0:.0f}s]')

nrep = 0
def repair(c):
    global nrep
    nrep += 1; tag = f'rep{nrep:03d}'
    st = os.path.join(a.out, tag + '_in.npz'); od = os.path.join(a.out, tag)
    np.savez(st, X=np.array([p[0] for p in c]), L=np.array([p[1] for p in c]), R=R)
    env = dict(os.environ, OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', MKL_NUM_THREADS='1', NUMEXPR_NUM_THREADS='1')
    with open(os.path.join(a.out, tag + '.log'), 'w') as lg:
        subprocess.run(['timeout', '900', 'nice', '-n', '15', sys.executable, os.path.join(HERE, 'mirror_sa4.py'),
                        str(1000 + nrep), od, '--init', st, '--secs', str(a.secs)],
                       stdout=lg, stderr=subprocess.STDOUT, env=env, check=False)
    b = np.load(os.path.join(od, 'best.npz'))
    return [(int(x), int(l)) for x, l in zip(b['X'], b['L'])]

for g in range(a.gens):
    parents = sorted(pop.values(), key=lambda v: -v[0])[:a.psize]
    cands = {}
    for _ in range(a.children):
        i, j = rr.sample(range(len(parents)), 2)
        c = make_child(parents[i][1], parents[j][1])
        kk = key(c)
        if not c or kk in cands or kk in pop: continue
        cands[kk] = (score(c), c)
    top = sorted(cands.values(), key=lambda v: -v[0])
    hist = {}
    for f0, _ in cands.values(): hist[f0] = hist.get(f0, 0) + 1
    P(f'gen {g}: screened {len(cands)} distinct children, F histogram {dict(sorted(hist.items(), reverse=True))} [{time.time()-t0:.0f}s]')
    for f0, c in top[:a.repair]:
        if a.deadline and time.time() > a.deadline:
            P('deadline reached, no more repairs'); break
        res = repair(c)
        Fr = score(res)
        P(f'  child screened F={f0} k={len(c)} -> repaired F={Fr} k={len(res)} [{time.time()-t0:.0f}s]')
        pop[key(res)] = (Fr, res)
        if Fr > best[0]:
            best = (Fr, res); save_best(Fr, res, f'gen {g}')
    pop = dict(sorted(pop.items(), key=lambda kv: -kv[1][0])[:2 * a.psize])
    P(f'gen {g} done, pop F:', sorted([v[0] for v in pop.values()], reverse=True))
P('FINAL best F', best[0], 'k', len(best[1]), f'[{time.time()-t0:.0f}s]')
