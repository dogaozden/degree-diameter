"""uncrowd.py K SEED TRIES: random K flags (p on l) with pairwise non-collinear points and pairwise disjoint lines.
Prints FLAGS "p:l ..." and the exact flag matching size (400 = exact sigma exists for all flags)."""
import sys, random
sys.path.insert(0, '.')
from gq import load, perp, lperp
from flagmatch import setup, hk
q, N, lines, lof = load('gq/gq_q7.bin')
P = [perp(lines, lof, p) for p in range(N)]
Lp = [lperp(lines, lof, l) for l in range(N)]
def search(k, rng):
    pts, lns = [], []
    order = list(range(N)); rng.shuffle(order)
    for p in order:
        if len(pts) == k: break
        if any(p in P[f] for f in pts): continue
        cand = [l for l in lof[p] if all(l not in Lp[m] for m in lns)]
        if not cand: continue
        pts.append(p); lns.append(rng.choice(cand))
    return list(zip(pts, lns)) if len(pts) == k else None
if __name__ == '__main__':
    k, seed, tries = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed); best = None; seen = {}
    for t in range(tries):
        fl = search(k, rng)
        if fl is None: continue
        adj = setup(q, N, lines, lof, fl)
        size, _ = hk(adj, N, N)
        seen[size] = seen.get(size, 0) + 1
        if best is None or size > best[0]:
            best = (size, fl)
        if size == N:
            break
    print('matching histogram', sorted(seen.items()))
    print('BEST', best[0], 'FLAGS', ' '.join(f'{p}:{l}' for p, l in best[1]))
