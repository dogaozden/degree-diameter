import sys
# usage: mkbase.py a b c d  -> 2+2 base [[a,b],[c,d]], side0 = {0,1}, side1 = {2,3}
a, b, c, d = map(int, sys.argv[1:5])
M = [[a, b], [c, d]]
edges = []
for i in range(2):
    for j in range(2):
        edges += [(i, 2 + j)] * M[i][j]
print(4, len(edges))
print("0 0 1 1")
for u, w in edges:
    print(u, w)
