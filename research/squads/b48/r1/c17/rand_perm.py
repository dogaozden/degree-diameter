# c17: random 2-generated permutation groups of degree 6..14 with order in 1094..1300 (nonabelian), 15 s budget.
import random, time, json
random.seed(7)
CAP = 1300
def closure(gens, n):
    ident = tuple(range(n)); seen = {ident}; els = [ident]; i = 0
    while i < len(els):
        g = els[i]; i += 1
        for s in gens:
            h = tuple(g[s[t]] for t in range(n))
            if h not in seen:
                seen.add(h); els.append(h)
                if len(els) > CAP: return None
    return els
t0 = time.time(); pairs = 0; hits = []
while time.time() - t0 < 15:
    n = random.randint(6, 14)
    # random permutations with few cycles (more likely to generate small groups)
    def rp():
        k = random.randint(2, 4)
        pts = list(range(n)); random.shuffle(pts)
        cuts = sorted(random.sample(range(1, n), k - 1)) if k > 1 else []
        p = list(range(n)); prev = 0
        for c in cuts + [n]:
            blk = pts[prev:c]; prev = c
            for i in range(len(blk)):
                p[blk[i]] = blk[(i + 1) % len(blk)]
        return tuple(p)
    a, b = rp(), rp()
    pairs += 1
    els = closure([a, b], n)
    if els is None or len(els) < 1094: continue
    # abelian test on generators
    def mul(x, y): return tuple(x[y[t]] for t in range(n))
    abel = mul(a, b) == mul(b, a)
    hits.append({"n": n, "order": len(els), "abelian_gens": abel, "a": a, "b": b})
print("pairs", pairs, "hits", len(hits), "time", round(time.time() - t0, 1))
for h in hits[:10]: print(h["n"], h["order"], h["abelian_gens"], h["a"], h["b"])
