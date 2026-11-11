# usage: rm.py in.edges matching.txt out.edges  -- delete matching edges from graph
import sys
inp, mt, outp = sys.argv[1:4]
f = open(inp); n = int(f.readline())
M = set()
for l in open(mt):
    a, b = map(int, l.split()); M.add((min(a,b), max(a,b)))
E = []
for l in f:
    if not l.strip(): continue
    a, b = map(int, l.split())
    if (min(a,b), max(a,b)) in M: M.discard((min(a,b), max(a,b))); continue
    E.append((a,b))
with open(outp, 'w') as g:
    g.write(f"{n}\n"); g.writelines(f"{a} {b}\n" for a,b in E)
print("removed; left", len(E), "unremoved matching edges", len(M))
