"""For a base file: C (recovered from sigma), S = {R : C(delta(R)) isotropic}, all hyperbolic lines h of W(8) with |S & h|,
and the best families of pairwise disjoint hyperbolic lines (usage: python3 hlines.py base.in)."""
import sys, itertools
sys.path.insert(0, "/home/user/degree-diameter/research/squads/r6-d11D5/c8")
from vstats import *
def hyperbolic_lines():
    H = set()
    for a in range(n0):
        for b in range(a + 1, n0):
            if Bf(PTS[a], PTS[b]): H.add(frozenset(span(PTS[a], PTS[b])))
    return list(H)
if __name__ == "__main__":
    t = open(sys.argv[1]).read().split(); n, dg = int(t[0]), int(t[1])
    sig = [int(x) for x in t[2 + n * dg:2 + n * dg + n]]
    M, C = recover_C(sig, n)
    S = set(R for R in range(n0) if is_W([C[p] for p in LINES[d_pt[R]][:2]]))
    H = hyperbolic_lines(); print("hyperbolic lines", len(H), " |S| =", len(S))
    from collections import Counter
    cnt = Counter(len(h & S) for h in H); print("histogram of |S & h| over hyperbolic lines:", sorted(cnt.items()))
    good = sorted([h for h in H if len(h & S) >= 7], key=lambda h: -len(h & S)); print("lines with >=7 S-points:", len(good))
    best = (0, None)
    import random
    rng = random.Random(5)
    for it in range(400000):
        if it > 0 and not good: break
        h1 = rng.choice(good); h2 = rng.choice(good)
        if h1 & h2: continue
        cands = [h for h in good if not (h & h1) and not (h & h2)]
        if not cands: continue
        h3 = max(cands, key=lambda h: len(h & S))
        val = min(len(h1 & S), len(h2 & S), len(h3 & S))
        tot = len(h1 & S) + len(h2 & S) + len(h3 & S)
        if (val, tot) > (best[0], best[1] if best[1] else 0):
            best = (val, tot, sorted(h1), sorted(h2), sorted(h3))
        if it > 3000: break
    print("best triple (min |S&h|, sum):", best[0], best[1]); print("h1", best[2]); print("h2", best[3]); print("h3", best[4])
