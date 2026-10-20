"""The Araujo-Pardo--Lopez core (and our +2 core) seen as a Delorme doubling plus patches, in PG(2,q).

A0 = {ell, A, X_s, AX_s : s in S}. Doubling with the ell-X_s and A-AX_s edges parallel (M~H_s, Q~K_s) and the
X_s-AX_s edges crossed (H_s ~ AX_s, X_s ~ K_s). Prints: degrees, the pairs at distance > 3 in the pure doubling,
and the edge difference between the AL core and the pure doubling.

python3 al_as_doubling.py q
"""
import sys
from collections import deque, Counter

from lift import ROOT

sys.path.insert(0, str(ROOT / 'research' / 'plus2'))
import construction as con  # noqa: E402

q = int(sys.argv[1])
points, lines = con.pg_plane(q)
A, ell, P, X = con.default_frame(points, lines)
for hats in (3, 4):
    S = X[:3] if hats == 3 else X
    AX = {x: con.line_through(lines, A, x) for x in lines[ell]}
    # pure doubling, in the same vertex names as construction.core_incidences
    inc = {(('p', p), ('l', j)) for j, L in enumerate(lines) for p in L}
    Cp = {A} | set(S)
    Cl = {ell} | {AX[s] for s in S}
    cp = {A: ('Q',), **{s: ('H', s) for s in S}}
    cl = {ell: ('M',), **{AX[s]: ('K', s) for s in S}}
    crossed = {(s, AX[s]) for s in S}
    for j, L in enumerate(lines):
        for p in L:
            if p in Cp and j in Cl:
                if (p, j) in crossed:
                    inc.add((cp[p], ('l', j)))
                    inc.add((('p', p), cl[j]))
                else:
                    inc.add((cp[p], cl[j]))
            elif p in Cp:
                inc.add((cp[p], ('l', j)))
            elif j in Cl:
                inc.add((('p', p), cl[j]))
    pts, lns, core = con.core_incidences(points, lines, q, A, ell, P, list(X), hats)
    if hats == 3:
        # AL has 3 hats; core_incidences(hats=3) uses X[:3] and no rotation
        pass
    n, edges, ids = con.to_graph(pts, lns, inc)
    name = {i: v for v, i in ids.items()}
    adj = [[] for _ in range(n)]
    deg = Counter()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        deg[u] += 1
        deg[v] += 1
    bad = []
    for s in range(n):
        d = [-1] * n
        d[s] = 0
        dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if d[y] < 0:
                    d[y] = d[x] + 1
                    dq.append(y)
        for t in range(s + 1, n):
            if d[t] > 3 or d[t] < 0:
                bad.append((name[s], name[t], d[t]))

    def label(v):
        if v[0] == 'p':
            x = v[1]
            return 'A' if x == A else f'X{S.index(x)}' if x in S else 'P' if x == P else 'pt(ell)' if x in lines[ell] else 'pt'
        if v[0] == 'l':
            j = v[1]
            for s in S:
                if j == AX[s]:
                    return f'AX{S.index(s)}'
            return 'ell' if j == ell else 'line'
        if v[0] in ('H', 'K'):
            return f'{v[0]}{S.index(v[1])}'
        return v[0]
    kinds = Counter(tuple(sorted((label(a), label(b)))) for a, b, _ in bad)
    print(f'q={q}, {hats} hats: pure doubling has {n} vertices, max degree {max(deg.values())}, '
          f'{len(bad)} pairs at distance > 3')
    for k, c in sorted(kinds.items()):
        print(f'   {k}: {c}')
    extra = sorted(set(core) - inc, key=str)
    miss = sorted(inc - set(core), key=str)
    print('   core minus doubling:', [(label(a), label(b)) for a, b in extra])
    print('   doubling minus core:', [(label(a), label(b)) for a, b in miss])
