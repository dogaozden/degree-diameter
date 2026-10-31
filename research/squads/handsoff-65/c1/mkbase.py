# usage: mkbase.py a OUT   -- 2+2 base [[a,6-a],[6-a,a]]: vertices 0,1 side 0; 2,3 side 1
import sys
a = int(sys.argv[1]); out = sys.argv[2]
edges = []
for (u, w, k) in [(0, 2, a), (0, 3, 6 - a), (1, 2, 6 - a), (1, 3, a)]:
    edges += [(u, w)] * k
with open(out, "w") as f:
    f.write("SOL\n%d %d\n0 0 1 1\n" % (4, len(edges)))
    for u, w in edges:
        f.write("%d %d\n" % (u, w))
