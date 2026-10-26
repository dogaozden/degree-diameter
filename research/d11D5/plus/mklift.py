"""Z6 lift (liftcheck format) of a plusopt base with doubled matching: flags get 3*nu, copies get 1 and 4.
nu file: one bit per flag, flag order = in2zc.py order (lines in order, points in listed order).
usage: python3 mklift.py base.in nu.txt out_lift.txt"""
import sys
f = open(sys.argv[1]); n, dg = map(int, f.readline().split())
L = [list(map(int, f.readline().split())) for _ in range(n)]
sig = [int(f.readline()) for _ in range(n)]
nu = [int(x) for x in open(sys.argv[2]).read().split()]
with open(sys.argv[3], "w") as g:
    g.write(f"{n} {n} 6\n"); k = 0
    for l in range(n):
        for p in L[l]: g.write(f"{p} {l} {3*nu[k]}\n"); k += 1
    for p in range(n):
        g.write(f"{p} {sig[p]} 1\n{p} {sig[p]} 4\n")
print("lift", 12 * n, "vertices")
