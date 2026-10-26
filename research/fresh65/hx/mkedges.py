# Build the Haar graph edge list (apsp format) from a haarex table file and an S (indices): (g,A)=g, (g,B)=N+g, edge g ~ N + s*g
import sys
f = open(sys.argv[1]).read().split()
N = int(f[0]); M = [int(x) for x in f[1:1 + N * N]]
S = [int(x) for x in sys.argv[2].split(',')]
with open(sys.argv[3], 'w') as o:
    o.write(f"{2 * N}\n")
    for g in range(N):
        for s in S: o.write(f"{g} {N + M[s * N + g]}\n")
