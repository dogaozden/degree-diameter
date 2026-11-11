#!/usr/bin/env python3
"""Which elements a [[1,5],[5,1]] pair misses, per condition, with element order and centrality.
usage: nearmiss.py TAB e1 e1 e1 e1 e1 e2 e2 e2 e2 e2"""
import sys
f = open(sys.argv[1]).read().split(); m = int(f[0]); T = [[int(f[1 + i * m + j]) for j in range(m)] for i in range(m)]
inv = [row.index(0) for row in T]
E1 = list(map(int, sys.argv[2:7])); E2 = list(map(int, sys.argv[7:12])); E = E1 + E2
def prod(*sets):
    r = {0}
    for S in sets: r = {T[a][b] for a in r for b in S}
    return r
I = lambda S: [inv[x] for x in S]
Q1, Q2, P1, P2 = prod(E1, I(E1)), prod(E2, I(E2)), prod(I(E1), E1), prod(I(E2), E2)
EEi, EiE = prod(E, I(E)), prod(I(E), E)
C = {'C1': EEi | prod(Q1, Q1), 'C2': EEi | prod(Q2, Q2), 'C3': EiE | prod(P2, P2), 'C4': EiE | prod(P1, P1),
     'C5': set(E) | prod(Q1, E1) | prod(Q1, E2) | prod(E1, P2) | prod(Q2, E2),
     'C6': set(E) | prod(Q1, E1) | prod(E2, P1) | prod(Q2, E1) | prod(Q2, E2)}
def order(x):
    k, y = 1, x
    while y: y = T[y][x]; k += 1
    return k
central = lambda x: all(T[x][y] == T[y][x] for y in range(m))
for k, S in C.items():
    miss = sorted(set(range(m)) - S)
    print(k, len(miss), [(x, 'ord', order(x), 'central' if central(x) else '') for x in miss])
