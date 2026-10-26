"""c8: K22 start with a C that maps two disjoint reguli delta(h1), delta(h2) into W (best of CT random C's).
usage: k22c.py seed CT out.in [starts]  -> writes the best of `starts` random placements (SCORE cost printed)."""
import sys, random, os, subprocess
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r5-d11D5/c8")
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *
from k22b import best_two
from k22 import score

def pick_C(rng, CT):
    best = None
    for t in range(CT):
        while True:
            M = randmat(rng); C = pmap(M)
            if sum(is_W([C[p] for p in l[:2]]) for l in LINES) < n0: break
        S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
        h1, h2 = best_two(S, rng)
        if h1 is None or h2 is None: continue
        val = len(S & set(h1)) + len(S & set(h2))
        if best is None or val > best[0]: best = (val, M, C, h1, h2)
    return best

def place(rng, M, C, h1, h2, out):
    col = [set() for _ in range(n0)]
    for l in LINES:
        for a in l: col[a].update(l)
    Cinv = pmap(matinv(M))
    rh1, rh2 = list(h1), list(h2); rng.shuffle(rh1); rng.shuffle(rh2)
    Ra, Ra2 = rh1[0], rh1[1]; Rb, Rb2 = rh2[0], rh2[1]
    Lflag = [d_pt[R] for R in rh1[2:]] + [d_pt[R] for R in rh2[2:]]
    if len(set(Lflag)) != 14 or d_pt[Ra] in Lflag or d_pt[Rb] in Lflag: return None
    usedP = set(); ps = {}; groups = {0: [], 1: []}
    order = list(range(14)); rng.shuffle(order)
    for idx in order:
        L = Lflag[idx]
        cand = [p for p in LINES[L] if p not in usedP]
        good = [p for p in cand if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]])]
        pool = good if good else cand
        rng.shuffle(pool); placed = False
        for p in pool:
            gs = [g for g in (0, 1) if len(groups[g]) < 7 and all(p not in col[q] for q in groups[g])]
            if not gs: continue
            g = rng.choice(gs); groups[g].append(p); usedP.add(p); ps[idx] = (p, g); placed = True; break
        if not placed: return None
    n = n0 + 2; X, Y = n0, n0 + 1; LS, MS = n0, n0 + 1
    L2 = [list(l) for l in LINES]
    for idx in range(14):
        L = Lflag[idx]; p, g = ps[idx]
        L2[L] = [(X if idx < 7 else Y) if q == p else q for q in L2[L]]
    L2.append(groups[0] + [X, Y]); L2.append(groups[1] + [X, Y])
    sig = [d_pt[C[p]] for p in range(n0)]
    lc, mc = (LS, MS) if rng.random() < 0.5 else (MS, LS)
    sig[Cinv[Ra]] = lc; sig[Cinv[Rb]] = mc
    sig.append(d_pt[Ra]); sig.append(d_pt[Rb])
    assert sorted(sig) == list(range(n))
    assert all(len(l) == 9 for l in L2) and len(L2) == n
    with open(out, "w") as f:
        f.write(f"{n} 9\n")
        for l in L2: f.write(" ".join(map(str, l)) + "\n")
        for s in sig: f.write(f"{s}\n")
    return True

if __name__ == "__main__":
    seed, CT, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    starts = int(sys.argv[4]) if len(sys.argv) > 4 else 20
    rng = random.Random(seed)
    val, M, C, h1, h2 = pick_C(rng, CT)
    print("C value", val, "h1", h1, "h2", h2, file=sys.stderr)
    best = None
    for t in range(starts):
        tmp = f"{out}.t{t}"
        if place(rng, M, C, h1, h2, tmp) is None: continue
        c = score(tmp); print("start", t, "cost", c, flush=True)
        if best is None or c < best[0]: best = (c, tmp)
    if best:
        os.replace(best[1], out); print("best", best[0], out)
