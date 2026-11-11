# usage: add_vertex.py base.edges sol.txt out.edges : add vertex y=n adjacent to the listed B-side vertices (ids)
import sys
base, sol, out = sys.argv[1:4]
f = open(base); n = int(f.readline())
S = [int(x) for x in open(sol) if x.strip()]
with open(out, 'w') as g:
    g.write(f"{n+1}\n")
    g.writelines(l for l in f)
    g.writelines(f"{n} {s}\n" for s in S)
print("n", n+1, "added degree", len(S))
