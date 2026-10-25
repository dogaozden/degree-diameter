"""Convert a graph file of Conder's census of cubic symmetric graphs (symmcubicgraphs.tar.gz, lines
'v  n1 n2 n3 ;', 1-based) to an apsp.c edge list (0-based). Usage: conder2edges.py IN OUT"""
import re, sys
adj = {}
for line in open(sys.argv[1]):
    m = re.match(r'\s*(\d+)\s+([\d\s]+);', line)
    if m:
        adj[int(m.group(1))] = list(map(int, m.group(2).split()))
n = len(adj)
assert sorted(adj) == list(range(1, n + 1))
E = sorted({(min(u, v) - 1, max(u, v) - 1) for u in adj for v in adj[u]})
for u in adj:
    for v in adj[u]:
        assert u in adj[v]
with open(sys.argv[2], 'w') as f:
    f.write(f'{n}\n')
    f.writelines(f'{u} {v}\n' for u, v in E)
print(sys.argv[2], n, len(E))
