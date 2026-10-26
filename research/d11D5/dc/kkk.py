"""KK "Kkk blocks" (k = env K, default 2; k new points all on k new lines) on W(8) (generalising squad r5 card c8's k22.py).  Block b: new points X, Y and new lines l, m with
X, Y on both l and m; X on 7 old lines delta(R), R in a hyperbolic line h (minus two points Ra, Ra2), Y likewise on
another hyperbolic line; each of these 14 old lines gives up one point, 7 to l and 7 to m (pairwise non-collinear).
sigma = delta o C on old points except sigma(C^-1(Ra)) = l, sigma(X) = delta(Ra) (same for Y, m).
Hyperbolic lines are chosen pairwise disjoint and far apart, maximising |h meet S| (S = points R with C(delta(R)) isotropic).
usage: k22x.py KK seed out.in [tries]"""
import sys, random, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gq import *
def score(path):
    out = subprocess.run(["/tmp/po7", path], env=dict(os.environ, SCORE="1"), capture_output=True, text=True).stdout
    return int(out.split("cost=")[1].split()[0])
col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)
def build(KK, seed, out):
    K = int(os.environ.get('K', '2')); CYC = os.environ.get('CYC') == '1'; rng = random.Random(seed)
    PAT = os.environ.get('PAT')
    if PAT:
        inc = [tuple(map(int, e.split('-'))) for e in PAT.split(',')]
        K = 1 + max(max(i for i, j in inc), max(j for i, j in inc)); KK = 1
        dpt = [sum(1 for i, j in inc if i == a) for a in range(K)]; dln = [sum(1 for i, j in inc if j == b) for b in range(K)]
    elif CYC: inc = [(j, j) for j in range(K)] + [(j, (j - 1) % K) for j in range(K)]
    else: inc = [(i, j) for i in range(K) for j in range(K)]
    if not PAT: dpt = [sum(1 for i, j in inc if i == a) for a in range(K)]; dln = [sum(1 for i, j in inc if j == b) for b in range(K)]
    DEG = 2 if CYC else K
    if os.environ.get('PLANE') == '1':
        import k22p
        M, C, S = k22p.parabolic_C(rng); Cinv = pmap(matinv(M)); S = set(S)
        P0 = [P for P in S if all(Bf(PTS[P], PTS[R]) == 0 for R in S)][0]
        R0 = rng.choice([R for R in S if R != P0])
        hyp = []
        for R in S:
            if R in (R0, P0): continue
            g = frozenset(span(PTS[R0], PTS[R]))
            if P0 in g or g in hyp: continue
            hyp.append(g)
        hs = [sorted(g - {R0}) for g in rng.sample(hyp, K * KK)]   # R0 is never used
    else:
        while True:
            M = randmat(rng); C = pmap(M)
            if sum(is_W([C[p] for p in l[:2]]) for l in LINES) < n0: break
        Cinv = pmap(matinv(M))
        S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
        hs = []; usedR = set(); nearP = set()
        for k in range(K * KK):
            best, bw = None, -1
            for _ in range(3000):
                a, b = rng.sample(range(n0), 2)
                if not Bf(PTS[a], PTS[b]): continue
                h = sorted(span(PTS[a], PTS[b]))
                if set(h) & usedR: continue
                Ls = [d_pt[R] for R in h]
                pass
                w = len(S & set(h)) + rng.random() * 0.5
                if w > bw: best, bw = h, w
            if best is None: print('no h', k); return None
            hs.append(best); usedR.update(best)
            for R in best: nearP.update(LINES[d_pt[R]])
    L2 = [list(l) for l in LINES]; sig = [d_pt[C[p]] for p in range(n0)]; newl = []; sig_new = []
    usedP = set()
    for b in range(KK):
        news = [n0 + K * b + j for j in range(K)]
        groups = {j: [] for j in range(K)}; jumps = []; tasks = []
        for j in range(K):
            h = hs[K * b + j]
            order = sorted(h, key=lambda R: (R in S, rng.random()))
            Ra = order[0]; jumps.append(Ra)
            keep = [R for R in sorted(h, key=lambda R: (R not in S, rng.random())) if R != Ra][:9 - dpt[j]]
            tasks += [(news[j], d_pt[R]) for R in keep]
        rng.shuffle(tasks)
        for which, L in tasks:
            cand = [p for p in LINES[L] if p not in usedP]
            good = [p for p in cand if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]])]
            ok = False
            for pool in (good, cand):
                pool = pool[:]; rng.shuffle(pool)
                for p in pool:
                    gs = [g for g in range(K) if len(groups[g]) < 9 - dln[g] and all(p not in col[q] for q in groups[g])]
                    if not gs: continue
                    g = rng.choice(gs); groups[g].append(p); usedP.add(p)
                    L2[L] = [which if q == p else q for q in L2[L]]; ok = True; break
                if ok: break
            if not ok: print('no p', b); return None
        lids = [n0 + K * b + j for j in range(K)]; rng.shuffle(lids)
        for j in range(K): newl.append(groups[j] + [news[i] for i, jj in inc if jj == j])
        for j in range(K): sig[Cinv[jumps[j]]] = lids[j]
        sig_new += [d_pt[R] for R in jumps]
    sig += sig_new; L2 += newl; n = n0 + K * KK
    if sorted(sig) != list(range(n)) or any(len(l) != 9 for l in L2): print('bad sig', len(set(sig)), n, [len(l) for l in L2 if len(l)!=9]); return None
    with open(out, "w") as f:
        f.write(f"{n} 9\n")
        for l in L2: f.write(" ".join(map(str, l)) + "\n")
        for s in sig: f.write(f"{s}\n")
    return True
if __name__ == "__main__":
    KK, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; tries = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    best = None
    for t in range(tries):
        tmp = out + f".t{t}"
        if not build(KK, seed * 1000 + t, tmp): continue
        c = score(tmp); print(f"try {t} cost {c}", flush=True)
        if best is None or c < best[0]:
            if best: os.remove(best[1])
            best = (c, tmp)
        else: os.remove(tmp)
    if best: os.replace(best[1], out); print("best", best[0], out)
