#!/usr/bin/env python3
# Distinct reduced words (free group on the non-tree edges, tree edges = 1) of the same-side walks of length 2 and 4
# from orbit i to orbit j (A side, mlift_chart conventions). Upper bound on distinct values for ANY group (nonabelian
# groups have no forced collisions beyond these). Abelian bound = distinct coefficient vectors (formal.py).
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d12D5-r1/c1')
from walkcount import load, need
from formal import tree_edges
def reduce_word(w):
    out = []
    for x in w:
        if out and out[-1][0] == x[0] and out[-1][1] == -x[1]: out.pop()
        else: out.append(x)
    return tuple(out)
def words(k, E, side):
    istree = tree_edges(k, E); ne = len(E)
    A = [e[0] for e in E] if side == 0 else [e[1] for e in E]
    B = [e[1] for e in E] if side == 0 else [e[0] for e in E]
    S = {}
    for i in range(k):
        for e1 in range(ne):
            if A[e1] != i: continue
            for e2 in range(ne):
                if B[e2] != B[e1] or e2 == e1: continue
                if side == 0: w = [(e2, -1), (e1, +1)]          # x = v(e2)^-1 v(e1)   (reads right-to-left as product)
                else:         w = [(e2, +1), (e1, -1)]          # x = v(e2) v(e1)^-1 ... (B side)
                S.setdefault((i, A[e2], 2), set()).add(reduce_word([t for t in w if not istree[t[0]]]))
                for e3 in range(ne):
                    if e3 == e2 or A[e3] != A[e2]: continue
                    for e4 in range(ne):
                        if e4 == e3 or B[e4] != B[e3]: continue
                        if side == 0: w = [(e4, -1), (e3, +1), (e2, -1), (e1, +1)]
                        else:         w = [(e4, +1), (e3, -1), (e2, +1), (e1, -1)]
                        S.setdefault((i, A[e4], 4), set()).add(reduce_word([t for t in w if not istree[t[0]]]))
    return S
if __name__ == '__main__':
    for p in sys.argv[1:]:
        k, E = load(p)
        S = words(k, E, 0)
        D = {}
        for (i, j, L), s in S.items(): D.setdefault((i, j), set()).update(s)
        cnt = [[len(D.get((i, j), ())) for j in range(k)] for i in range(k)]
        print(p.split('/')[-1], 'distinct reduced words A-side', cnt)
        for n in (24, 25, 26, 27):
            print('   n', n, 'min(distinct words - need) =', min(cnt[i][j] - need(n, k, i, j) for i in range(k) for j in range(k)))
