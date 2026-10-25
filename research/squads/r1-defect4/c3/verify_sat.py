#!/usr/bin/env python3
"""Independent check of a SAT answer from gen_type.py + kissat.
usage: verify_sat.py k kissat_output_file
Decodes the model (point x line incidence N), then checks on the FULL bipartite graph (2n vertices, networkx):
max degree k, bipartite, diameter 3 (order 2(k^2-k-1)). Prints the cycle type of the point repeat graph R_X = NN^T-(k-1)I-J.
"""
import sys, itertools
import networkx as nx
import numpy as np

k = int(sys.argv[1])
n = k * k - k - 1
lits = set()
for line in open(sys.argv[2]):
    if line.startswith('v'):
        lits.update(int(t) for t in line.split()[1:])
# variable ids: IDPool order of first use in gen_type.build: X[(p,l)] created first, in row-major order -> id = p*n+l+1
N = np.zeros((n, n), dtype=int)
for p in range(n):
    for l in range(n):
        N[p, l] = 1 if (p * n + l + 1) in lits else 0
assert (N.sum(axis=0) == k).all() and (N.sum(axis=1) == k).all(), 'degree check failed'
G = nx.Graph()
G.add_nodes_from(range(2 * n))
for p, l in zip(*np.nonzero(N)):
    G.add_edge(int(p), int(n + l))
assert nx.is_bipartite(G)
deg = max(d for _, d in G.degree())
diam = nx.diameter(G)
ok = (deg == k) and (diam == 3) and G.number_of_nodes() == 2 * (k * k - k - 1)
Gram = N @ N.T
R = Gram - (k - 1) * np.eye(n, dtype=int) - np.ones((n, n), dtype=int)
R_graph = nx.MultiGraph()
R_graph.add_nodes_from(range(n))
for x in range(n):
    for y in range(x + 1, n):
        for _ in range(int(R[x, y])):
            R_graph.add_edge(x, y)
cyc = sorted((len(c) if len(c) > 2 else 2 for c in nx.connected_components(R_graph)), reverse=True)
comp_sizes = sorted((len(c) for c in nx.connected_components(R_graph)), reverse=True)
print(f'k={k} n={n} maxdeg={deg} diameter={diam} order={G.number_of_nodes()} valid={ok} '
      f'R_X component sizes={comp_sizes}')
