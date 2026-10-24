"""Expand a liftcheck input (base edges with Z_M voltages) into an explicit edge list for apsp.c.
Vertex (a, g) of side A -> a*M + g; vertex (b, g) of side B -> (nA + b)*M + g.
usage: python3 lift2edges.py lift.txt out.edges"""
import sys
src, out = sys.argv[1], sys.argv[2]
with open(src) as f:
    nA, nB, M = map(int, f.readline().split())
    base = [tuple(map(int, line.split())) for line in f if line.strip()]
n = (nA + nB) * M
with open(out, "w") as fo:
    fo.write(f"{n}\n")
    for a, b, v in base:
        for g in range(M):
            fo.write(f"{a*M + g} {(nA + b)*M + (g + v) % M}\n")
print(f"{out}: {n} vertices, {len(base)*M} edges")
