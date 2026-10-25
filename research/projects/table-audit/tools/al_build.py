"""Write the Araujo-Pardo--Lopez graph (problems/bipartite_dd/lib.py, transcribed from arXiv 2005.02427) as an edge list
for apsp.c (table-audit). Usage: al_build.py q OUT. q = 9, 11, 13 give the table's (11,3) 190, (13,3) 274, (15,3) 374."""
import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../../../problems/bipartite_dd'))
import lib

q, out = int(sys.argv[1]), sys.argv[2]
g = lib.araujo_lopez_graph(q)
if isinstance(g, tuple):
    n, E = g[0], g[1]
else:
    n, E = g.number_of_nodes(), list(g.edges())
with open(out, 'w') as f:
    f.write(f'{n}\n')
    f.writelines(f'{u} {v}\n' for u, v in E)
print(out, n, len(E))
