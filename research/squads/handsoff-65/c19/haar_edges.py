# usage: python3 -I haar_edges.py GROUPFILE "s1 s2 ... s6" OUT.edges   (Haar graph H(G,S): (0,g)~(1,g*s))
import sys
gf, S, out = sys.argv[1], [int(x) for x in sys.argv[2].split()], sys.argv[3]
with open(gf) as f:
    n = int(f.readline())
    M = [list(map(int, f.readline().split())) for _ in range(n)]
E = []
for g in range(n):
    for s in S:
        E.append((g, n + M[g][s]))
with open(out, "w") as f:
    f.write(f"{2*n}\n")
    for u, v in E:
        f.write(f"{u} {v}\n")
print("wrote", out, 2*n, "vertices", len(E), "edges")
