#!/usr/bin/env python3
"""Symmetric 2+2 base, side-PRESERVING sigma' = (A1 A2)(B1 B2): vertices 0=A1,1=A2 (side 0), 2=B1,3=B2 (side 1).
usage: mksym2.py a BASE_OUT SYM_OUT
  classes A=(0,2)xa, B=(0,3)x(6-a), C=(1,2)x(6-a), D=(1,3)xa. sigma' maps A->D and B->C (pairs, index by index).
  Voltage rule: volt(partner) = theta(volt(rep)); with theta = id (FMAP identity) the lift has the automorphism
  (v,h) -> (sigma' v, h). SYM: ptype 0 = rep, 1 = partner, same format as mksym.py."""
import sys
a = int(sys.argv[1]); bout, sout = sys.argv[2], sys.argv[3]
edges = []; idx = {}
def add_class(key, u, w, k):
    for j in range(k):
        idx[(key, j)] = len(edges); edges.append([u, w, None, None])
add_class('A', 0, 2, a); add_class('D', 1, 3, a); add_class('B', 0, 3, 6 - a); add_class('C', 1, 2, 6 - a)
for j in range(a):
    x, y = idx[('A', j)], idx[('D', j)]; edges[x][2:] = [0, y]; edges[y][2:] = [1, x]
for j in range(6 - a):
    x, y = idx[('B', j)], idx[('C', j)]; edges[x][2:] = [0, y]; edges[y][2:] = [1, x]
with open(bout, 'w') as f:
    f.write("SOL\n4 %d\n0 0 1 1\n" % len(edges))
    for u, w, _, _ in edges: f.write("%d %d 0\n" % (u, w))
with open(sout, 'w') as f:
    for _, _, t, p in edges: f.write("%d %d\n" % (t, p))
print("edges", len(edges), "reps", sum(1 for e in edges if e[2] == 0))
