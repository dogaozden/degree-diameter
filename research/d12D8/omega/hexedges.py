"""hexq6 output -> edge list of the incidence graph (points 0..n-1, lines n..2n-1). usage: hexedges.py hex.txt out.txt"""
import sys
f = open(sys.argv[1]); q, n, nl = map(int, f.readline().split())
with open(sys.argv[2], 'w') as o:
    o.write(f"{n + nl}\n")
    for l in range(nl):
        for p in f.readline().split(): o.write(f"{p} {n + l}\n")
