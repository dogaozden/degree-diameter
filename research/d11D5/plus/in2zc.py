import sys
f = open(sys.argv[1]); n, dg = map(int, f.readline().split())
L = [list(map(int, f.readline().split())) for _ in range(n)]
sig = [int(f.readline()) for _ in range(n)]
E = []; nf = 0
for l in range(n):
    for p in L[l]: E.append((p, n + l, 0, nf)); nf += 1
for J in (4, 1):
    for p in range(n): E.append((p, n + sig[p], J, -1))
with open(sys.argv[2], "w") as g:
    g.write(f"{2*n} {nf} 0 3\n"); g.writelines("%d %d %d %d\n" % e for e in E)
