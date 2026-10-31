# filter.py BASE [G1 G2 ...]: girth-type filter for lifts of BASE to diameter 9.
# BASE: "b m" + edges, or "n" + edges (seed format, m = n*4/2 inferred). Edge-level non-backtracking walks (multigraph safe).
# For every root u: closed walks at u of length 2..9 (need >= |G|-1 distinct non-identity voltages), and for every
# target v the walks u->v of length <= 9 (need >= |G| voltages). Prints per-base minima and the verdict per |G|.
import sys
from collections import defaultdict
def load(fn):
    L = [l.split() for l in open(fn) if l.strip()]
    if len(L[0]) == 2:
        b, m = int(L[0][0]), int(L[0][1]); E = [(int(a), int(c)) for a, c in L[1:1+m]]
    else:
        b = int(L[0][0]); E = [(int(a), int(c)) for a, c in L[1:]]
    return b, E
def counts(b, E, u, Lmax=9):
    inc = [[] for _ in range(b)]
    for j, (x, y) in enumerate(E):
        inc[x].append((y, j)); inc[y].append((x, j))
    # state: dict (vertex, last_edge) -> count of NB walks of current length from u
    cur = defaultdict(int)
    for y, j in inc[u]: cur[(y, j)] += 1
    walks_to = [0]*b; closed = 0
    walks_to_len = [0]*b
    for y, j in inc[u]: walks_to[y] += 1
    for y, j in inc[u]:
        if y == u: closed += 1
    for L in range(2, Lmax+1):
        nxt = defaultdict(int)
        for (x, pj), c in cur.items():
            for y, j in inc[x]:
                if j != pj: nxt[(y, j)] += c
        cur = nxt
        for (x, j), c in cur.items():
            walks_to[x] += c
            if x == u: closed += c
    return walks_to, closed
def main():
    fn = sys.argv[1]; Gs = [int(g) for g in sys.argv[2:]]
    b, E = load(fn)
    deg = [0]*b
    for x, y in E: deg[x] += 1; deg[y] += 1
    minW = None; minC = None; tot = None
    for u in range(b):
        w, c = counts(b, E, u)
        s = sum(w)
        tot = s if tot is None else tot
        mw = min(w[v] for v in range(b) if v != u or True)
        minW = mw if minW is None else min(minW, mw)
        minC = c if minC is None else min(minC, c)
    print(f"{fn}: b={b} m={len(E)} degrees={sorted(set(deg))} total NB walks<=9 per root={tot} "
          f"min over roots of closed walks={minC}, min over (root,target) walks={minW}")
    for G in Gs:
        print(f"  |G|={G}: closed need {G-1} -> {'PASS' if minC >= G-1 else 'FAIL'}; target need {G} -> {'PASS' if minW >= G else 'FAIL'}")
main()
