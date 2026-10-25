#!/usr/bin/env python3
# For each base: walks from orbit i to orbit j (same side) as formal linear forms over the free voltages
# (abelian groups). Distinct forms per (i,j) bound the number of distinct values an ABELIAN group can produce.
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d12D5-r1/c1')
from walkcount import load, need
def tree_edges(k, E):
    ne = len(E); seen = [False] * (2 * k); seen[0] = True; q = [0]; h = 0; istree = [False] * ne
    while h < len(q):
        x = q[h]; h += 1
        for i, (a, b) in enumerate(E):
            bb = k + b
            y = -1
            if x == a and not seen[bb]: y = bb
            elif x == bb and not seen[a]: y = a
            if y >= 0: seen[y] = True; q.append(y); istree[i] = True
    return istree
def forms(k, E, side):
    istree = tree_edges(k, E)
    free = [e for e in range(len(E)) if not istree[e]]
    A = [e[0] for e in E] if side == 0 else [e[1] for e in E]
    B = [e[1] for e in E] if side == 0 else [e[0] for e in E]
    ne = len(E); F = {}
    for i in range(k):
        for e1 in range(ne):
            if A[e1] != i: continue
            for e2 in range(ne):
                if B[e2] != B[e1] or e2 == e1: continue
                vec = [0] * ne; vec[e1] += 1; vec[e2] -= 1  # sign convention irrelevant for counting
                F.setdefault((i, A[e2], 2), set()).add(tuple(vec[f] for f in free))
                for e3 in range(ne):
                    if e3 == e2 or A[e3] != A[e2]: continue
                    for e4 in range(ne):
                        if e4 == e3 or B[e4] != B[e3]: continue
                        v = [0] * ne; v[e1] += 1; v[e2] -= 1; v[e3] += 1; v[e4] -= 1
                        F.setdefault((i, A[e4], 4), set()).add(tuple(v[f] for f in free))
    return F
if __name__ == '__main__':
    for p in sys.argv[1:]:
        k, E = load(p)
        for side in (0,):
            F = forms(k, E, side)
            # distinct forms over all lengths for each (i,j)
            D = {}
            for (i, j, L), s in F.items():
                D.setdefault((i, j), set()).update(s)
            cnt = [[len(D.get((i, j), ())) for j in range(k)] for i in range(k)]
            # total walks per (i,j)
            tot = [[sum(len(s) for (a, b, L), s in F.items() if a == i and b == j) for j in range(k)] for i in range(k)]
            print(p.split('/')[-1], 'distinct forms', cnt, 'walks', tot)
            for n in (24, 25, 26, 27):
                sl = min(cnt[i][j] - need(n, k, i, j) for i in range(k) for j in range(k))
                print('   n', n, 'min(distinct forms - need) =', sl)
