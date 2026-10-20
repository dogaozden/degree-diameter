"""Random test of Lemma 2: in a generalized n-gon, a single doubling with (b) keeps the diameter n iff every
component of G[A] has diameter <= n-2. Builds random A by greedy insertion under (b) and checks both directions.

python3 test_lemma2.py {gq|hex} q TRIALS
"""
import random
import sys
from collections import deque

from lift import lib, gq_edges, lift, max_degree, diameter, ROOT
from gq_clones import q4

kind, q, trials = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
if kind == 'gq':
    pts, lines, _ = q4(q)
    n = len(pts)
    E = gq_edges(n, lines)
    V, D = n + len(lines), 4
else:
    sys.path.insert(0, str(ROOT / 'research' / 'gh6'))
    import gh_build
    n, lines = gh_build.hexagon(q)
    E = gq_edges(n, lines)
    V, D = 2 * n, 6
nb = [[] for _ in range(V)]
for u, w in E:
    nb[u].append(w)
    nb[w].append(u)


def comp_diams(A):
    A = set(A)
    seen, out = set(), []
    for s in A:
        if s in seen:
            continue
        comp, dq = {s}, deque([s])
        while dq:
            x = dq.popleft()
            for y in nb[x]:
                if y in A and y not in comp:
                    comp.add(y)
                    dq.append(y)
        seen |= comp
        best = 0
        for c in comp:
            dist = {c: 0}
            dq = deque([c])
            while dq:
                x = dq.popleft()
                for y in nb[x]:
                    if y in comp and y not in dist:
                        dist[y] = dist[x] + 1
                        dq.append(y)
            best = max(best, max(dist.values()))
        out.append(best)
    return out


rng = random.Random(1)
agree = 0
for t in range(trials):
    A, seen_by = set(), [0] * V
    target = [D - 2, D - 1, D][t % 3]  # component diameter aimed at in this trial

    def can_add(y):
        return y not in A and all(seen_by[z] == 0 for z in nb[y] if z not in A)

    def add(y):
        A.add(y)
        for z in nb[y]:
            seen_by[z] += 1
    for _ in range(6):  # a few components
        free = [x for x in range(V) if seen_by[x] == 0 and can_add(x)]
        if not free:
            break
        comp = [rng.choice(free)]
        add(comp[0])
        for _ in range(60):
            if max(comp_diams(comp)) >= target:
                break
            ext = [y for c in comp for y in nb[c] if seen_by[y] == 1 and can_add(y)]
            if not ext:
                break
            y = rng.choice(ext)
            add(y)
            comp.append(y)
    Nn, H = lift(V, E, A)
    dmax, _ = max_degree(Nn, H)
    diam = diameter(Nn, H)
    md = max(comp_diams(A))
    pred = md <= D - 2
    ok = (diam <= D) == pred and dmax <= q + 2
    agree += ok
    print(f'trial {t}: |A|={len(A)} max comp diam {md} -> diameter {diam}, max degree {dmax}, '
          f'lemma predicts {"<=" if pred else ">"} {D}: {"agree" if ok else "DISAGREE"}', flush=True)
print(f'{agree}/{trials} agree')
