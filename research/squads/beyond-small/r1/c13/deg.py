import sys, collections
f = open(sys.argv[1]); n = int(f.readline())
deg = [0]*n; E = []
for line in f:
    a, b = map(int, line.split()); E.append((a, b)); deg[a] += 1; deg[b] += 1
print("n", n, "edges", len(E), "maxdeg", max(deg))
print("degree histogram", sorted(collections.Counter(deg).items()))
