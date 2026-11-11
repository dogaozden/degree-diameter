"""Referee check of Theorem 5.14 (regular graphs of diameter 6) for q=3, m=2,3 and q=5, m=2: deletion as in the
proof, then a completion found by the swap argument of Lemma 5.13; regularity and diameter checked by apsp64."""
import sys, itertools, random
import d6_ref
from hexagon import write_edges
def run(q, m):
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()):
        H, lvl, _ = d6_ref.run(q, ms=())
    N = H.N
    v = next(k for k in range(N) if lvl[('L', k)] == 2)
    S1 = [k for k in range(N) if lvl[('L', k)] == 1]
    R = set(S1[:q])
    ver = {}
    for x, l in lvl.items():
        for w in itertools.product(range(m), repeat=l + 1):
            # deletions of Theorem 5.14
            if x == ('L', v) and w[2] >= 1: continue
            if x[0] == 'L' and x[1] in S1 and x[1] not in R and w[1] >= 1: continue
            ver[(x, w)] = len(ver)
    isP = {idx: (x[0] == 'P') for (x, w), idx in ver.items()}
    edges = set()
    for k in range(N):
        for i in H.lines[k]:
            for wl in itertools.product(range(m), repeat=lvl[('L', k)] + 1):
                if (('L', k), wl) not in ver: continue
                for wp in itertools.product(range(m), repeat=lvl[('P', i)] + 1):
                    s_ = min(len(wl), len(wp))
                    if wl[:s_] == wp[:s_]: edges.add((ver[(('P', i), wp)], ver[(('L', k), wl)]))
    n = len(ver); nP = sum(isP.values()); nL = n - nP
    D = q + m; deg = [0] * n
    for a, b in edges: deg[a] += 1; deg[b] += 1
    assert max(deg) <= D and min(deg) >= D - (m - 1), (min(deg), max(deg))
    # Lemma 5.13: multiset, then swaps
    Jp = [x for x in range(n) if isP[x] for _ in range(D - deg[x])]
    Jl = [x for x in range(n) if not isP[x] for _ in range(D - deg[x])]
    assert len(Jp) == len(Jl), (len(Jp), len(Jl))
    random.seed(1); random.shuffle(Jl)
    J = list(zip(Jp, Jl))
    def bad_entries():
        cnt = {}
        for e in J: cnt[e] = cnt.get(e, 0) + 1
        return [t for t, e in enumerate(J) if e in edges or cnt[e] > 1]
    it = 0
    while True:
        bads = bad_entries()
        if not bads: break
        t = bads[0]; p, L = J[t]
        while True:
            u = random.randrange(len(J)); p2, L2 = J[u]
            if u != t and (p2, L) not in edges and (p, L2) not in edges and (p2, L) not in J and (p, L2) not in J: break
        J[t] = (p, L2); J[u] = (p2, L); it += 1
    all_edges = list(edges) + J
    write_edges(f"thmR_q{q}_m{m}.edges", n, all_edges)
    formula = 2*(q+1)*(q**4+q*q+1+(m-1)*(q**3+m+1))
    print(f"q={q} m={m}: after deletion {nP} points, {nL} lines, deficits <= {m-1}; T={len(J)}; swaps {it}; order {n} (formula {formula})")
for a in sys.argv[1:]:
    q, m = map(int, a.split(','))
    run(q, m)
