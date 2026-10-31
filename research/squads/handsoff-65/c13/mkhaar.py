# build Haar graph H(G,S): A_x ~ B_y iff x^-1 y in S, G = group table (m, then m*m entries row-major, 0 = identity)
import sys
tab = open(sys.argv[1]).read().split()
m = int(tab[0]); T = [[int(tab[1 + i * m + j]) for j in range(m)] for i in range(m)]
S = [int(s) for s in sys.argv[2].split(',')]
out = sys.argv[3]
inv = [0] * m
for x in range(m):
    for y in range(m):
        if T[x][y] == 0: inv[x] = y
E = []
for x in range(m):
    for s in S:
        y = T[x][s]  # x * s  -> need x^-1 y = s  => y = x*s
        E.append((x, m + y))
with open(out, 'w') as f:
    f.write(f"{2*m}\n")
    for a, b in E: f.write(f"{a} {b}\n")
print("vertices", 2*m, "edges", len(E))
