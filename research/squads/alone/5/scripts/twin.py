# Twin construction: x (new A) gets N(x)=N(a*), y (new B) gets N(y)=N(b*).
# Requires a perfect matching of 16 existing edges (a_i,b_i), a_i in N(b*), b_i in N(a*); those edges are removed.
# Usage: twin.py base.e out.e A_STAR B_STAR   (A_STAR in 0..nA-1, B_STAR as a B-index 0..nA-1)
import sys
from graph import load
def matching(adjA, Ns, Nb):
    """perfect matching between Ns (A-ids) and Nb (B-ids, global) along edges; returns dict a->b or None"""
    mate = {}
    def aug(a, seen):
        for b in adjA[a]:
            if b in Nb and b not in seen:
                seen.add(b)
                if b not in mate or aug(mate[b], seen):
                    mate[b] = a; return True
        return False
    for a in Ns:
        if not aug(a, set()): return None
    return {a: b for b, a in mate.items()}
if __name__ == '__main__':
    path, out, astar, bstar = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    n, adj, E = load(path)
    nA = n // 2
    Bstar = nA + bstar
    NAstar = set(adj[astar])          # B-ids (global)
    NBstar = set(adj[Bstar])          # A-ids
    m = matching(adj, NBstar, NAstar)
    if m is None:
        print('NO PERFECT MATCHING'); sys.exit(3)
    removed = {(min(a, b), max(a, b)) for a, b in m.items()}
    # new numbering: A 0..nA (x = nA), B nA+1 .. 2nA+1 (old B id v -> v+1, y = 2nA+1)
    x = nA; y = 2 * nA + 1
    newE = []
    for u, v in E:
        if (min(u, v), max(u, v)) in removed: continue
        newE.append((u, v + 1))
    newE += [(x, b + 1) for b in NAstar]
    newE += [(a, y) for a in NBstar]
    N = 2 * nA + 2
    with open(out, 'w') as f:
        f.write(f'{N}\n'); f.writelines(f'{u} {v}\n' for u, v in newE)
    print('wrote', out, 'n', N, 'edges', len(newE), 'removed', len(removed), 'a*', astar, 'b*', bstar, 'a*~b*', Bstar in adj[astar])
