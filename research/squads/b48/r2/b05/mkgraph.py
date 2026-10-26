# usage: mkgraph.py e1 e2 e3 OUT.edges   (same surgery as triples.c)
import sys
L = open('/home/user/degree-diameter/research/squads/b48/r2/b05/classes.txt').read().split('\n')[1:]
E = [tuple(map(int, l.split()[:2])) for l in L if l.strip()]
es = [int(t) for t in sys.argv[1:4]]
out = sys.argv[4]
dele = set(es)
edges = [e for i, e in enumerate(E) if i not in dele]
a = [E[i][0] for i in es]; b = [E[i][1] for i in es]
x, y = 2184, 2185
edges += [(x, bi) for bi in b] + [(x, y)] + [(y, ai) for ai in a]
with open(out, 'w') as f:
    f.write('2186\n')
    for u, v in edges: f.write('%d %d\n' % (u, v))
