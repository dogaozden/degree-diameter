"""KK "K22 blocks" on W(8) (generalising squad r5 card c8's k22.py).  Block b: new points X, Y and new lines l, m with
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
    rng = random.Random(seed)
    while True:
        M = randmat(rng); C = pmap(M)
        if sum(is_W([C[p] for p in l[:2]]) for l in LINES) < n0: break
    Cinv = pmap(matinv(M))
    S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
    hs = []; usedR = set(); nearP = set()
    for k in range(2 * KK):
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
        X, Y = n0 + 2 * b, n0 + 2 * b + 1
        groups = {0: [], 1: []}; jumps = []
        for which, h in ((X, hs[2 * b]), (Y, hs[2 * b + 1])):
            order = sorted(h, key=lambda R: (R in S, rng.random()))
            om = order[:2]; rng.shuffle(om); Ra = om[0]
            flag = [R for R in h if R not in om]
            for R in flag:
                L = d_pt[R]
                cand = [p for p in LINES[L] if p not in usedP]
                good = [p for p in cand if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]])]
                pool = good if good else cand; rng.shuffle(pool)
                ok = False
                for p in pool:
                    gs = [g for g in (0, 1) if len(groups[g]) < 7 and all(p not in col[q] for q in groups[g])]
                    if not gs: continue
                    g = rng.choice(gs); groups[g].append(p); usedP.add(p)
                    L2[L] = [which if q == p else q for q in L2[L]]; ok = True; break
                if not ok: print('no p', b); return None
            jumps.append(Ra)
        lid, mid = n0 + 2 * b, n0 + 2 * b + 1
        newl.append(groups[0] + [X, Y]); newl.append(groups[1] + [X, Y])
        lc, mc = (lid, mid) if rng.random() < 0.5 else (mid, lid)
        sig[Cinv[jumps[0]]] = lc; sig[Cinv[jumps[1]]] = mc
        sig_new += [d_pt[jumps[0]], d_pt[jumps[1]]]
    sig += sig_new; L2 += newl; n = n0 + 2 * KK
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
