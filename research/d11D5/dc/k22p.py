"""KK K22 blocks with all hyperbolic lines through one point R0 of the plane S = P0^perp, where C keeps exactly the
W-lines meeting the axis delta(P0) isotropic (parabolic congruence).  Every switch line delta(R), R in S, stays
isotropic under C.  Each h omits R0 and one jump point Ra (sigma(C^-1(Ra)) = new line, sigma(new point) = delta(Ra)).
usage: k22p.py KK seed out.in [tries]"""
import sys, random, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gq import *
def score(path):
    out = subprocess.run(["/tmp/po7", path], env=dict(os.environ, SCORE="1"), capture_output=True, text=True).stdout
    return int(out.split("cost=")[1].split()[0])
col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)
def parabolic_C(rng):
    while True:   # require three lines of a grid regulus to stay isotropic (this gives the parabolic type)
        a, b = rng.sample(range(n0), 2)
        if not Bf(PTS[a], PTS[b]): continue
        h = sorted(span(PTS[a], PTS[b])); Ls = [d_pt[R] for R in h]
        for _ in range(20000):
            M = randmat(rng); C = pmap(M)
            if all(is_W([C[p] for p in LINES[L][:2]]) for L in Ls[:3]):
                S = [R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]])]
                if len(S) == 73: return M, C, S
def build(KK, seed, out):
    rng = random.Random(seed)
    M, C, S = parabolic_C(rng); Cinv = pmap(matinv(M)); Sset = set(S)
    P0 = [P for P in S if all(Bf(PTS[P], PTS[R]) == 0 for R in S)][0]
    R0 = rng.choice([R for R in S if R != P0])
    hyp = []
    for R in S:
        if R in (R0, P0): continue
        g = frozenset(span(PTS[R0], PTS[R]))
        if P0 in g or g in hyp: continue
        hyp.append(g)
    assert len(hyp) == 8 and all(g <= Sset for g in hyp)
    hs = [sorted(g) for g in rng.sample(hyp, 2 * KK)]
    L2 = [list(l) for l in LINES]; sig = [d_pt[C[p]] for p in range(n0)]; newl = []; sig_new = []; usedP = set()
    for b in range(KK):
        X, Y = n0 + 2 * b, n0 + 2 * b + 1
        groups = {0: [], 1: []}; jumps = []; tasks = []
        for which, h in ((X, hs[2 * b]), (Y, hs[2 * b + 1])):
            rest = [R for R in h if R != R0]; Ra = rng.choice(rest); jumps.append(Ra)
            tasks += [(which, d_pt[R]) for R in rest if R != Ra]
        rng.shuffle(tasks)
        for which, L in tasks:
            cand = [p for p in LINES[L] if p not in usedP]
            good = [p for p in cand if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]])]
            ok = False
            for pool in (good, cand):
                pool = pool[:]; rng.shuffle(pool)
                for p in pool:
                    gs = [g for g in (0, 1) if len(groups[g]) < 7 and all(p not in col[q] for q in groups[g])]
                    if not gs: continue
                    g = rng.choice(gs); groups[g].append(p); usedP.add(p)
                    L2[L] = [which if q == p else q for q in L2[L]]; ok = True; break
                if ok: break
            if not ok: return None
        lid, mid = n0 + 2 * b, n0 + 2 * b + 1
        newl.append(groups[0] + [X, Y]); newl.append(groups[1] + [X, Y])
        lc, mc = (lid, mid) if rng.random() < 0.5 else (mid, lid)
        sig[Cinv[jumps[0]]] = lc; sig[Cinv[jumps[1]]] = mc
        sig_new += [d_pt[jumps[0]], d_pt[jumps[1]]]
    sig += sig_new; L2 += newl; n = n0 + 2 * KK
    if sorted(sig) != list(range(n)) or any(len(l) != 9 for l in L2): return None
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
        if not build(KK, seed * 1000 + t, tmp): print(f"try {t} failed", flush=True); continue
        c = score(tmp); print(f"try {t} cost {c}", flush=True)
        if best is None or c < best[0]:
            if best: os.remove(best[1])
            best = (c, tmp)
        else: os.remove(tmp)
    if best: os.replace(best[1], out); print("best", best[0], out)
