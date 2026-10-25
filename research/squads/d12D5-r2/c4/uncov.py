#!/usr/bin/env python3
"""Independent check (pure Python) of the FAKE cover of a k=1 voltage tuple: A-side and B-side uncovered elements.
usage: uncov.py TABLE v0,v1,v2,v3"""
import sys
v = open(sys.argv[1]).read().split(); n = int(v[0]); T = [[int(v[1 + i * n + j]) for j in range(n)] for i in range(n)]
e = next(i for i in range(n) if all(T[i][j] == j for j in range(n)))
inv = [next(j for j in range(n) if T[i][j] == e) for i in range(n)]
mul = lambda a, b: T[a][b]
volt = [int(x) for x in sys.argv[2].split(',')]
def words_A():
    W = set()
    for a in range(4):
        for b in range(4):
            if b == a: continue
            W.add(mul(inv[volt[b]], volt[a]))
            for c in range(4):
                if c == b: continue
                for d in range(4):
                    if d == c: continue
                    W.add(mul(inv[volt[d]], mul(volt[c], mul(inv[volt[b]], volt[a]))))
    return W
def words_B():
    W = set()
    for a in range(4):
        for b in range(4):
            if b == a: continue
            W.add(mul(volt[b], inv[volt[a]]))
            for c in range(4):
                if c == b: continue
                for d in range(4):
                    if d == c: continue
                    W.add(mul(volt[d], mul(inv[volt[c]], mul(volt[b], inv[volt[a]]))))
    return W
WA = words_A() | {e}; WB = words_B() | {e}
UA = [g for g in range(n) if g not in WA]; UB = [g for g in range(n) if g not in WB]
def order(g):
    k, x = 1, g
    while x != e: x = mul(x, g); k += 1
    return k
print('n', n, 'tuple', volt, 'uncovered A', [(g, order(g)) for g in UA], 'uncovered B', [(g, order(g)) for g in UB])
print('B-side = A-side of inverse tuple:', sorted(UB) == sorted([g for g in range(n) if g not in {x for x in WA}]) if False else '')
