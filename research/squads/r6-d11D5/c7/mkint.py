"""c7 (wildcard): switch block with MIXED sigma.  K new points X_j and K new lines g (ids n0+j), incidences from
PAT ("i-j,..." new point i on new line j).  Each new point j has one of two sigma types (MODE string, one letter per j):
  J (jump, as in kkk.py): sigma(X_j) = delta(Ra_j) (an old line), sigma(C^-1(Ra_j)) = a new line.  The old points keep
      sigma = delta o C everywhere else.
  I (internal): sigma(X_j) = a new line (no old point changes its sigma).  The new block is self-contained for sigma,
      so the bulk stays delta o C on all 585 old points.
Old lines through X_j: delta(R) for R on a hyperbolic line h_j (9 - deg(X_j) of them; J points exclude Ra_j).  Each such
old line gives up one old point to a new line (rules as kkk.py: moved points on one new line are pairwise non-collinear,
each old point moves at most once).
usage: PAT="0-0,0-1,..." MODE=JJJ python3 mkint.py seed out.in [tries]     (SCORE via /tmp/po7, prints cost)
"""
import sys, random, os, subprocess
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5/dc")
from gq import *

col = [set() for _ in range(n0)]
for l in LINES:
    for a in l: col[a].update(l)


def score(path):
    out = subprocess.run(["/tmp/po7", path], env=dict(os.environ, SCORE="1"), capture_output=True, text=True).stdout
    return int(out.split("cost=")[1].split()[0])


def build(inc, modes, rng, out):
    K = len(modes)
    dpt = [sum(1 for i, j in inc if i == a) for a in range(K)]
    dln = [sum(1 for i, j in inc if j == b) for b in range(K)]
    while True:
        M = randmat(rng); C = pmap(M)
        if sum(is_W([C[p] for p in l[:2]]) for l in LINES) < n0: break
    Cinv = pmap(matinv(M))
    S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
    hs = []; usedR = set()
    for j in range(K):
        best, bw = None, -1
        for _ in range(3000):
            a, b = rng.sample(range(n0), 2)
            if not Bf(PTS[a], PTS[b]): continue
            h = sorted(span(PTS[a], PTS[b]))
            if set(h) & usedR: continue
            w = len(S & set(h)) + rng.random() * 0.5
            if w > bw: best, bw = h, w
        if best is None: return None
        hs.append(best); usedR.update(best)
    jumps = [None] * K; keeps = [None] * K
    SPLIT = os.environ.get('SPLIT') == '1'
    if SPLIT:   # second hyperbolic line per new point: old lines drawn from both (half and half)
        hs2 = []
        for j in range(K):
            best, bw = None, -1
            for _ in range(3000):
                a, b = rng.sample(range(n0), 2)
                if not Bf(PTS[a], PTS[b]): continue
                h = sorted(span(PTS[a], PTS[b]))
                if set(h) & usedR: continue
                w = len(S & set(h)) + rng.random() * 0.5
                if w > bw: best, bw = h, w
            if best is None: return None
            hs2.append(best); usedR.update(best)
    for j in range(K):
        h = hs[j]
        if modes[j] == 'J':
            Ra = sorted(h, key=lambda R: (R in S, rng.random()))[0]; jumps[j] = Ra
            cands = [R for R in sorted(h, key=lambda R: (R not in S, rng.random())) if R != Ra]
        else:
            cands = sorted(h, key=lambda R: (R not in S, rng.random()))
        if SPLIT:
            a = (9 - dpt[j]) // 2; b = 9 - dpt[j] - a
            hb = sorted(hs2[j], key=lambda R: (R not in S, rng.random()))
            keeps[j] = cands[:a] + hb[:b]
        else:
            keeps[j] = cands[:9 - dpt[j]]
    L2 = [list(l) for l in LINES]
    usedP = set(); groups = [[] for _ in range(K)]
    tasks = [(n0 + j, d_pt[R]) for j in range(K) for R in keeps[j]]
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
        if not ok: return None
    for g in range(K):
        for i, gg in inc:
            if gg == g: groups[g].append(n0 + i)
        L2.append(groups[g])
    sig = [d_pt[C[p]] for p in range(n0)]
    I_idx = [j for j in range(K) if modes[j] == 'I']; J_idx = [j for j in range(K) if modes[j] == 'J']
    lp = list(range(K)); rng.shuffle(lp)
    sig_new = [None] * K
    # internal: new point j -> new line that it is not on (avoid doubling a flag)
    free = lp[:]
    for j in I_idx:
        cands = [g for g in free if (j, g) not in inc]
        if not cands: cands = free
        g = rng.choice(cands); free.remove(g); sig_new[j] = n0 + g
    for j in J_idx:
        g = free.pop(0)
        Ra = jumps[j]; sig[Cinv[Ra]] = n0 + g; sig_new[j] = d_pt[Ra]
    sig += sig_new
    n = n0 + K
    if sorted(sig) != list(range(n)) or any(len(l) != 9 for l in L2) or len(L2) != n: return None
    for l in L2:
        if len(set(l)) != 9: return None
    with open(out, "w") as f:
        f.write(f"{n} 9\n")
        for l in L2: f.write(" ".join(map(str, l)) + "\n")
        for s in sig: f.write(f"{s}\n")
    return True


if __name__ == "__main__":
    seed, out = int(sys.argv[1]), sys.argv[2]
    tries = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    inc = [tuple(map(int, e.split('-'))) for e in os.environ['PAT'].split(',')]
    modes = list(os.environ.get('MODE', 'J' * (1 + max(max(i for i, j in inc), max(j for i, j in inc)))))
    best = None
    for t in range(tries):
        tmp = out + f".t{t}"
        if not build(inc, modes, random.Random(seed * 1000 + t), tmp):
            print("try", t, "failed"); continue
        c = score(tmp); print(f"try {t} cost {c}", flush=True)
        if best is None or c < best[0]:
            if best: os.remove(best[1])
            best = (c, tmp)
        else:
            os.remove(tmp)
    if best:
        os.replace(best[1], out); print("best", best[0], out)
