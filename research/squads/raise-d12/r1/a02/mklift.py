# usage: mklift.py GROUPFILE BASEFILE VOLTFILE OUT   (voltfile: "m cost" line then cotree voltages line)
# writes OUT: first line n, then "u v" edges of the lift; vertex (u,g) -> u*m+g; edge (u,g)-(v,g*a).
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/raise-d12/r1/a02')
from groups import readg
m, t = readg(sys.argv[1])
with open(sys.argv[2]) as f:
    n, ne = map(int, f.readline().split())
    be = [tuple(map(int, f.readline().split())) for _ in range(ne)]
with open(sys.argv[3]) as f:
    f.readline(); volts = list(map(int, f.readline().split()))
cot = [i for i, (u, v, tr) in enumerate(be) if tr == 0]
volt = {i: 0 for i in range(ne)}
for k, i in enumerate(cot): volt[i] = volts[k]
edges = []
for i, (u, v, tr) in enumerate(be):
    a = volt[i]
    for g in range(m):
        edges.append((u * m + g, v * m + t[g * m + a]))
with open(sys.argv[4], 'w') as f:
    f.write(f"{n*m}\n")
    for x, y in edges: f.write(f"{x} {y}\n")
print("lift vertices", n*m, "edges", len(edges))
