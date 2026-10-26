"""c8 (wildcard): K22 switch.  Two new points x*, y* and two new lines l*, m* with x*, y* both on l* and m*.
x* lies on the 7 old lines delta(R), R in h1 minus {Ra, Ra2}, and sigma(x*) = delta(Ra).  y* lies on the 7 old
lines delta(R), R in h2 minus {Rb, Rb2}, and sigma(y*) = delta(Rb).  Each of the 14 flagged old lines L loses one
point p_L (flag (p_L, L) removed) and p_L joins l* (7 points) or m* (7 points); the points on l* (resp. m*) are
pairwise non-collinear.  sigma^-1(l*) = C^-1(Ra), sigma^-1(m*) = C^-1(Rb) (or swapped); sigma = delta o C elsewhere.
Degrees: x*, y*, l*, m* have 7 + 2 = 9 neighbours, every old vertex keeps degree 9.
usage: k22.py seed out.in [tries]   (writes the best of `tries` random starts to out.in, prints its SCORE cost)"""
import sys, random, os, subprocess
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *

PO7 = "/tmp/po7"

def score(path):
    env = dict(os.environ, SCORE="1", THREADS="1")
    out = subprocess.run([PO7, path], env=env, capture_output=True, text=True).stdout
    for tok in out.split():
        if tok.startswith("cost="): return int(tok[5:])
    raise RuntimeError(out)

def hyp_lines(rng, k, weight):
    """k random hyperbolic lines; returns the one maximising weight(h) (ties random)."""
    best, bw = None, -1
    for _ in range(k):
        a, b = rng.sample(range(n0), 2)
        if not Bf(PTS[a], PTS[b]): continue
        h = sorted(span(PTS[a], PTS[b])); w = weight(h) + rng.random() * 0.5
        if w > bw: best, bw = h, w
    return best

def build(seed, out):
    rng = random.Random(seed)
    col = [set() for _ in range(n0)]
    for l in LINES:
        for a in l: col[a].update(l)
    # collineation C (not symplectic)
    while True:
        M = randmat(rng); C = pmap(M)
        pres = sum(is_W([C[p] for p in l[:2]]) for l in LINES)
        if pres < n0: break
    Cinv = pmap(matinv(M))
    # S = points R whose line delta(R) is mapped into W by C
    S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
    h1 = hyp_lines(rng, 4000, lambda h: len(S & set(h)))
    h2 = hyp_lines(rng, 4000, lambda h: len(S & set(h)) if not (set(h) & set(h1)) else -5)
    if h1 is None or h2 is None: return None
    def split(h):
        # two omitted points: prefer the ones outside S; jump = the first of them
        order = sorted(h, key=lambda R: (R in S, rng.random()))
        om = order[:2]; rng.shuffle(om)
        flag = [R for R in h if R not in om]
        return om[0], om[1], [d_pt[R] for R in flag], flag
    Ra, Ra2, F1, flag1 = split(h1)
    Rb, Rb2, F2, flag2 = split(h2)
    Lflag = F1 + F2
    if len(set(Lflag)) != 14 or d_pt[Ra] in Lflag or d_pt[Rb] in Lflag: return None
    # removed points: one per flagged line, good if C^-1(delta(p)) is a W-line
    usedP = set(); ps = {}
    groups = {0: [], 1: []}  # 0 -> l*, 1 -> m*
    order = list(range(14)); rng.shuffle(order)
    for idx in order:
        L = Lflag[idx]
        cand = [p for p in LINES[L] if p not in usedP]
        good = [p for p in cand if is_W([Cinv[q] for q in LINES[d_pt[p]][:2]])]
        pool = good if good else cand
        rng.shuffle(pool)
        placed = False
        for p in pool:
            # group with room and no collinear partner
            gs = [g for g in (0, 1) if len(groups[g]) < 7 and all(p not in col[q] for q in groups[g])]
            if not gs: continue
            g = rng.choice(gs)
            groups[g].append(p); usedP.add(p); ps[idx] = (p, g); placed = True
            break
        if not placed: return None
    n = n0 + 2
    X, Y = n0, n0 + 1          # new points x*, y*
    LS, MS = n0, n0 + 1        # new lines l*, m*
    L2 = [list(l) for l in LINES]
    for idx in range(14):
        L = Lflag[idx]; p, g = ps[idx]
        newpt = X if idx < 7 else Y
        L2[L] = [newpt if q == p else q for q in L2[L]]
    L2.append(groups[0] + [X, Y]); L2.append(groups[1] + [X, Y])
    sig = [d_pt[C[p]] for p in range(n0)]
    lc, mc = (LS, MS) if rng.random() < 0.5 else (MS, LS)
    sig[Cinv[Ra]] = lc; sig[Cinv[Rb]] = mc
    sig.append(d_pt[Ra]); sig.append(d_pt[Rb])
    assert sorted(sig) == list(range(n)), "sigma not a bijection"
    assert all(len(l) == 9 for l in L2) and len(L2) == n
    with open(out, "w") as f:
        f.write(f"{n} 9\n")
        for l in L2: f.write(" ".join(map(str, l)) + "\n")
        for s in sig: f.write(f"{s}\n")
    return dict(h1=h1, h2=h2, Ra=Ra, Rb=Rb, S1=len(S & set(h1)), S2=len(S & set(h2)))

if __name__ == "__main__":
    seed, out = int(sys.argv[1]), sys.argv[2]
    tries = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    best = None
    for t in range(tries):
        s = seed * 1000 + t
        tmp = out + f".t{t}"
        info = build(s, tmp)
        if info is None: continue
        c = score(tmp)
        print(f"try {t} seed {s} cost {c} S1={info['S1']} S2={info['S2']}", flush=True)
        if best is None or c < best[0]: best = (c, tmp)
    if best:
        os.replace(best[1], out); print("best", best[0], out)
