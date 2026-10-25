#!/usr/bin/env python3
# Group-free necessary condition for a k=3 base: number of non-backtracking walks of length 2 and 4
# (same side, as mlift_chart counts them with the fake chart) from source orbit i to target orbit j.
# A cover needs walks(i->j) >= n for j != i and >= n-1 for j == i (DIAGW=1), n = group order.
import sys, itertools
def load(path):
    with open(path) as f:
        k = int(f.readline()); E = [tuple(map(int, f.readline().split())) for _ in range(4 * k)]
    return k, E
def counts(k, E, side):
    # side 0: walks from A-orbits; side 1: from B-orbits (swap roles of EA/EB)
    A = [e[0] for e in E] if side == 0 else [e[1] for e in E]
    B = [e[1] for e in E] if side == 0 else [e[0] for e in E]
    ne = len(E); C = [[0] * k for _ in range(k)]
    for i in range(k):
        for e1 in range(ne):
            if A[e1] != i: continue
            for e2 in range(ne):
                if B[e2] != B[e1] or e2 == e1: continue
                C[i][A[e2]] += 1                      # 2-walk (e1,e2)
                for e3 in range(ne):
                    if e3 == e2 or A[e3] != A[e2]: continue
                    for e4 in range(ne):
                        if e4 == e3 or B[e4] != B[e3]: continue
                        C[i][A[e4]] += 1              # 4-walk
    return C
def need(n, k, i, j):
    return n - 1 if i == j else n
if __name__ == '__main__':
    for p in sys.argv[1:]:
        k, E = load(p)
        CA, CB = counts(k, E, 0), counts(k, E, 1)
        def slack(C, n):
            return min(C[i][j] - need(n, k, i, j) for i in range(k) for j in range(k))
        row = []
        for n in (24, 25, 26, 27):
            row.append(f"n{n}:A{slack(CA,n):+d}/B{slack(CB,n):+d}")
        print(p.split('/')[-1], 'A', CA, 'B', CB, ' '.join(row))
