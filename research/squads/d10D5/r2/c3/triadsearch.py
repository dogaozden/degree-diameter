"""triadsearch.py K TRIES SEED: randomized DFS for k freed flags whose every pair and triple satisfies the
necessary Hall conditions  |A_S \\ Fpts| <= |Ll_S \\ Flines|  and  |G_S \\ Flines| <= |Pp_S \\ Fpts|  (S = 2 or 3 flags),
then the exact matching (obst.py) decides.  Prints FLAGS / SIGMA when the matching is perfect."""
import sys, random, time, json
sys.path.insert(0, '.')
from obst import Geo
K = int(sys.argv[1]); TRIES = int(sys.argv[2]); seed = int(sys.argv[3])
rng = random.Random(seed)
geo = Geo(); N = geo.N
pc = lambda m: bin(m).count('1')
FS = {}
def sets(p, l):
    if (p, l) not in FS: FS[(p, l)] = geo.flag_sets(p, l)
    return FS[(p, l)]
flags_all = [(p, l) for p in range(N) for l in geo.lof[p]]
def ok_with(chosen, cand):
    """cand (p,l) compatible with chosen list under all pair and triple necessary conditions"""
    p0, l0 = cand
    Fpts = 0; Flin = 0
    for p, l in chosen: Fpts |= 1 << p; Flin |= 1 << l
    Fpts |= 1 << p0; Flin |= 1 << l0
    if any(p == p0 or l == l0 for p, l in chosen): return False
    base = [sets(p, l) for p, l in chosen] + [sets(p0, l0)]
    names = len(chosen)
    # pairs (i, new) and triples (i, j, new)
    for i in range(len(chosen)):
        Ai, Lli, Gi, Ppi = sets(*chosen[i]); Af, Llf, Gf, Ppf = sets(p0, l0)
        if pc((Ai & Af) & ~Fpts) > pc((Lli & Llf) & ~Flin): return False
        if pc((Gi & Gf) & ~Flin) > pc((Ppi & Ppf) & ~Fpts): return False
        for j in range(i):
            Aj, Llj, Gj, Ppj = sets(*chosen[j])
            A = Ai & Aj & Af; L = Lli & Llj & Llf; G = Gi & Gj & Gf; Pp = Ppi & Ppj & Ppf
            if pc(A & ~Fpts) > pc(L & ~Flin): return False
            if pc(G & ~Flin) > pc(Pp & ~Fpts): return False
    return True
def attempt():
    chosen = []
    while len(chosen) < K:
        order = flags_all[:]; rng.shuffle(order)
        found = None
        for c in order:
            if ok_with(chosen, c): found = c; break
        if found is None: return None
        chosen.append(found)
    return chosen
t0 = time.time(); best = None
for t in range(TRIES):
    ch = attempt()
    if ch is None: continue
    size, mL, _ = geo.matching(ch)
    d = N - size
    if best is None or d < best[0]: best = (d, ch); print('try', t, 'deficiency', d, 'flags', ch, 'time %.1f' % (time.time() - t0), flush=True)
    if d == 0:
        print('FOUND k', K, 'FLAGS', ' '.join(f'{p}:{l}' for p, l in ch))
        print('SIGMA', ' '.join(map(str, mL)))
        break
print('END k', K, 'tries', TRIES, 'best', best[0] if best else None, 'time %.1f' % (time.time() - t0))
