"""Triangle cycle block (tri.py) with moved points chosen for the new LINES: N_j = {X_j, X_{j+1}} + 7 moved points;
sigma(X_j) = delta(Q_j), sigma(X_{j+1}) = delta(Q_{j+1}) lie on delta(h_{j+1}); a moved point p = C^-1(R'), R' a switch
point of h_{j+1}, has sigma(p) = delta(R') on it too, so sigma(points of N_j) -> delta(PG-line).  p must sit on a switch
line: R = phi(R') = delta(p) meet S must be a switch point (distinct).  Triangles are sampled to maximise such hits;
the other moved points are chosen as in tri.py.  usage: tri2.py seed out.in [tries] [samples]"""
import sys, random, os, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gq import *
import k22p
def score(path):
    out = subprocess.run(["/tmp/po7", path], env=dict(os.environ, SCORE="1"), capture_output=True, text=True).stdout
    return int(out.split("cost=")[1].split()[0])
col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)
K = 3
def build(seed, out, samples):
    rng = random.Random(seed)
    M, C, S = k22p.parabolic_C(rng); Cinv = pmap(matinv(M)); Sset = set(S)
    P0 = [P for P in S if all(Bf(PTS[P], PTS[R]) == 0 for R in S)][0]
    phi = {}
    for Rp in S:
        inter = [R for R in LINES[d_pt[Cinv[Rp]]] if R in Sset]
        if len(inter) == 1: phi[Rp] = inter[0]
    pts = [R for R in S if R != P0]
    best = None
    for _ in range(samples):
        Q = rng.sample(pts, K)
        if any(Bf(PTS[Q[j - 1]], PTS[Q[j]]) == 0 for j in range(K)): continue
        hs = [sorted(span(PTS[Q[j - 1]], PTS[Q[j]])) for j in range(K)]
        if any(P0 in h for h in hs) or Q[2] in hs[1]: continue
        SW = {}
        for j in range(K):
            for R in hs[j]:
                if R not in Q: SW[R] = j
        hits = []; usedR = set()
        for j in range(K):        # moved points of N_j come from switch points R' of side h_{j+1}
            jj = (j + 1) % K
            for Rp in hs[jj]:
                if Rp in Q: continue
                R = phi.get(Rp)
                if R is not None and R in SW and R not in usedR and Cinv[Rp] in LINES[d_pt[R]]:
                    hits.append((j, Rp, R)); usedR.add(R)
        if best is None or len(hits) > len(best[2]): best = (Q, hs, hits, SW)
    if best is None: return None
    Q, hs, hits, SW = best
    news = [n0 + j for j in range(K)]
    L2 = [list(l) for l in LINES]; sig = [d_pt[C[p]] for p in range(n0)]
    groups = {j: [] for j in range(K)}; usedP = set(); doneL = set()
    for j, Rp, R in hits:
        p = Cinv[Rp]; L = d_pt[R]
        if len(groups[j]) >= 7 or p in usedP or any(p in col[q] for q in groups[j]): continue
        groups[j].append(p); usedP.add(p); doneL.add(L)
        L2[L] = [news[SW[R]] if q == p else q for q in L2[L]]
    tasks = [(news[SW[R]], d_pt[R]) for R in SW if d_pt[R] not in doneL]; rng.shuffle(tasks)
    for which, L in tasks:
        cand = [p for p in L2[L] if p < n0 and p not in usedP]
        good = [p for p in cand if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]])]
        ok = False
        for pool in (good, cand):
            pool = pool[:]; rng.shuffle(pool)
            for p in pool:
                gs = [g for g in range(K) if len(groups[g]) < 7 and all(p not in col[q] for q in groups[g])]
                if not gs: continue
                g = rng.choice(gs); groups[g].append(p); usedP.add(p)
                L2[L] = [which if q == p else q for q in L2[L]]; ok = True; break
            if ok: break
        if not ok: return None
    newl = [groups[j] + [news[j], news[(j + 1) % K]] for j in range(K)]
    for j in range(K): sig[Cinv[Q[j]]] = news[j]
    sig += [d_pt[Q[j]] for j in range(K)]
    L2 += newl; n = n0 + K
    if sorted(sig) != list(range(n)) or any(len(set(l)) != 9 for l in L2): return None
    with open(out, "w") as f:
        f.write(f"{n} 9\n")
        for l in L2: f.write(" ".join(map(str, l)) + "\n")
        for s in sig: f.write(f"{s}\n")
    return len(hits)
if __name__ == "__main__":
    seed, out = int(sys.argv[1]), sys.argv[2]; tries = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    samples = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
    best = None
    for t in range(tries):
        tmp = out + f".t{t}"
        h = build(seed * 1000 + t, tmp, samples)
        if not h and h != 0: print(f"try {t} failed", flush=True); continue
        c = score(tmp); print(f"try {t} hits {h} cost {c}", flush=True)
        if best is None or c < best[0]:
            if best: os.remove(best[1])
            best = (c, tmp)
        else: os.remove(tmp)
    if best: os.replace(best[1], out); print("best", best[0], out)
