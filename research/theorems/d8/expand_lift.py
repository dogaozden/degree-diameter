"""Expand a voltage lift (liftdiam format, Z_M1 x Z_M2) into an explicit edge list for apsp.c.
usage: python3 expand_lift.py base.txt out_edges.txt"""
import sys

with open(sys.argv[1]) as fh:
    NB, M1, M2, E = map(int, fh.readline().split())
    M = M1 * M2
    out = []
    for _ in range(E):
        u, v, a, b = map(int, fh.readline().split())
        for g1 in range(M1):
            for g2 in range(M2):
                h1, h2 = (g1 + a) % M1, (g2 + b) % M2
                out.append((u * M + g1 * M2 + g2, v * M + h1 * M2 + h2))
with open(sys.argv[2], 'w') as fh:
    fh.write(f'{NB * M}\n')
    fh.writelines(f'{x} {y}\n' for x, y in out)
