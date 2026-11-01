import sys
# usage: mkedges.py BASE n VOLTFILE OUT  (voltage file lines "edge_index volt"; edges indexed as base file order, edges 0..E-1)
base, n, vf, outf = sys.argv[1], int(sys.argv[2]), sys.argv[3], sys.argv[4]
L = open(base).read().split()
b = int(L[0]); E = (len(L) - 1) // 2
eu = [int(L[1 + 2 * e]) for e in range(E)]; ev = [int(L[2 + 2 * e]) for e in range(E)]
volt = [0] * E
# free edges set in liftd: edges not in BFS spanning tree; for voltage 0 default on tree edges.
for line in open(vf):
    p = line.split()
    if len(p) == 2: volt[int(p[0])] = int(p[1]) % n
with open(outf, "w") as f:
    f.write(f"{b*n}\n")
    for e in range(E):
        for g in range(n):
            f.write(f"{eu[e]*n+g} {ev[e]*n+(g+volt[e])%n}\n")
print("edges", E * n)
