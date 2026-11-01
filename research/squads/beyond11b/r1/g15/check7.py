# Side-B invariance (Theorem 1 for W'_h) and explicit h=3 closure/mod-6 check for -I (Delta=6).
import random, sys, itertools
from check import *
rng = random.Random(31)
bad = 0
for t in range(60):
    S = random_S(2, rng); dist = bfs(S)
    for gi in range(N):
        if dist[1][N+gi] != dist[1][N+A_al[gi]] or dist[1][N+gi] != dist[1][N+A_inv[gi]]: bad += 1
print("side-B alpha/inversion violations over 60 S (Delta=6):", bad)
h = 3; ok = 0; cnts = []
def prod(seq):
    g = e
    for (s,t) in seq: g = mul(g, mul(inv(s), t))
    return g
def rot(q): return q[1:]+q[:1]
def rev(q): return tuple((t,s) for (s,t) in reversed(q))
def al(q): return tuple((alpha(s),alpha(t)) for (s,t) in q)
for t in range(4):
    S = random_S(2, rng)
    pairs = [(s,u) for s in S for u in S]
    Q = [q for q in itertools.product(pairs, repeat=h) if prod(q) == mI]
    QS = set(Q)
    closed = all(rot(q) in QS and rev(q) in QS and al(q) in QS for q in Q)
    cnts.append(len(Q)); ok += closed and len(Q) % 6 == 0
    print("trial", t, "count", len(Q), "closed", closed, "count%6", len(Q)%6)
print("closed and count%6==0 in", ok, "of 4")
