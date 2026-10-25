"""Convert a neighbour-list file (line i = neighbours of vertex i; '#' lines are comments) to an apsp.c edge list.
Indices are 0-based unless --one-based. Checks symmetry. Usage: adjlist2edges.py IN OUT [--one-based]"""
import sys
off = 1 if '--one-based' in sys.argv else 0
rows = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip() and not l.lstrip().startswith('#')]
n = len(rows)
adj = [set(x - off for x in r) for r in rows]
for u in range(n):
    for v in adj[u]:
        assert 0 <= v < n and u in adj[v], (u, v)
E = sorted((u, v) for u in range(n) for v in adj[u] if u < v)
with open(sys.argv[2], 'w') as f:
    f.write(f'{n}\n')
    f.writelines(f'{u} {v}\n' for u, v in E)
print(sys.argv[2], n, len(E))
