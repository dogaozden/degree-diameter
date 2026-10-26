# Build the Cayley graph Cay(G, S) edge list (x ~ x*s) from a table file. Usage: edges.py TAB S1,S2,S3 OUT.edges
import sys
tab, S, out = sys.argv[1], [int(s) for s in sys.argv[2].split(',')], sys.argv[3]
with open(tab) as fh:
    N = int(fh.readline())
    T = [list(map(int, fh.readline().split())) for _ in range(N)]
E = set()
for x in range(N):
    for s in S:
        y = T[x][s]
        if x != y:
            E.add((min(x, y), max(x, y)))
with open(out, 'w') as fh:
    fh.write(f'{N}\n')
    for x, y in sorted(E):
        fh.write(f'{x} {y}\n')
print('N', N, 'edges', len(E))
