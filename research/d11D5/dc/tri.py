"""Cycle block of K new pairs with the hyperbolic lines forming a closed polygon in the plane S = P0^perp of a
parabolic C: X_j on new lines N_j and N_{j-1}; h_j = line(Q_{j-1}, Q_j); X_j on the 7 old lines delta(R),
R in h_j minus {Q_{j-1}, Q_j}; sigma(C^-1(Q_j)) = N_j, sigma(X_j) = delta(Q_j).  Then sigma^-1(pencil of X_j) =
C^-1(h_j), a full PG-line, and every switch line stays isotropic under C.  K = 3 (triangle).  For K = 4 the two
diagonal intersections h1^h3, h2^h4 are switch points of two new points (that old line takes both).
usage: tri.py K seed out.in [tries]"""
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
def build(K, seed, out):
    rng = random.Random(seed)
    M, C, S = k22p.parabolic_C(rng); Cinv = pmap(matinv(M)); Sset = set(S)
    P0 = [P for P in S if all(Bf(PTS[P], PTS[R]) == 0 for R in S)][0]
    for _ in range(1000):   # polygon Q_0..Q_{K-1} in S, all sides hyperbolic, no three Q collinear
        Q = rng.sample([R for R in S if R != P0], K)
        hs = [sorted(span(PTS[Q[j - 1]], PTS[Q[j]])) for j in range(K)]
        if any(P0 in h for h in hs): continue
        if any(Bf(PTS[Q[j - 1]], PTS[Q[j]]) == 0 for j in range(K)): continue
        if any(Q[(j + 1) % K] in hs[j] for j in range(K)): continue   # no three consecutive collinear
        break
    else: return None
    news = [n0 + j for j in range(K)]
    L2 = [list(l) for l in LINES]; sig = [d_pt[C[p]] for p in range(n0)]
    groups = {j: [] for j in range(K)}; usedP = set(); tasks = []
    for j in range(K):
        for R in hs[j]:
            if R in (Q[j - 1], Q[j]): continue
            tasks.append((news[j], d_pt[R]))
    rng.shuffle(tasks)
    for which, L in tasks:
        cand = [p for p in L2[L] if p < n0 and p not in usedP]
        good = [p for p in cand if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]])]
        j = which - n0; prefer = [j, (j + 1) % K]   # X_j lies on N_j and N_{j-1}; its moved points go to a line through it
        prefer = [j, (j - 1) % K]
        ok = False
        for pool in (good, cand):
            pool = pool[:]; rng.shuffle(pool)
            for p in pool:
                gs = [g for g in range(K) if len(groups[g]) < 7 and all(p not in col[q] for q in groups[g])]
                if not gs: continue
                gp = [g for g in gs if g not in prefer] or gs   # moved points go to a new line NOT through X_j when possible
                g = rng.choice(gp); groups[g].append(p); usedP.add(p)
                L2[L] = [which if q == p else q for q in L2[L]]; ok = True; break
            if ok: break
        if not ok: return None
    newl = [groups[j] + [news[j], news[(j + 1) % K]] for j in range(K)]   # N_j holds X_j and X_{j+1}
    for j in range(K):
        sig[Cinv[Q[j]]] = news[j]
    sig += [d_pt[Q[j]] for j in range(K)]
    L2 += newl; n = n0 + K
    if sorted(sig) != list(range(n)) or any(len(l) != 9 for l in L2) or any(len(set(l)) != 9 for l in L2): return None
    with open(out, "w") as f:
        f.write(f"{n} 9\n")
        for l in L2: f.write(" ".join(map(str, l)) + "\n")
        for s in sig: f.write(f"{s}\n")
    return True
if __name__ == "__main__":
    K, seed, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]; tries = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    best = None
    for t in range(tries):
        tmp = out + f".t{t}"
        if not build(K, seed * 1000 + t, tmp): print(f"try {t} failed", flush=True); continue
        c = score(tmp); print(f"try {t} cost {c}", flush=True)
        if best is None or c < best[0]:
            if best: os.remove(best[1])
            best = (c, tmp)
        else: os.remove(tmp)
    if best: os.replace(best[1], out); print("best", best[0], out)
