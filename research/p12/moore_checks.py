# Build known Moore graphs and write graph6 for the lbm filter.
# Heawood (3,6), Tutte 8-cage (3,8) via LCF, PG(2,3) incidence graph (4,6) built directly.
import itertools, sys
import networkx as nx

def pg23_incidence():
    # points of PG(2,3): nonzero vectors of GF(3)^3 up to scalar (normalised: first nonzero entry = 1)
    pts = []
    for v in itertools.product(range(3), repeat=3):
        if any(v) and next(x for x in v if x) == 1:
            pts.append(v)
    G = nx.Graph()
    for i, p in enumerate(pts):
        for j, l in enumerate(pts):
            if sum(a * b for a, b in zip(p, l)) % 3 == 0:
                G.add_edge(('p', i), ('l', j))
    return G

heawood = nx.LCF_graph(14, [5, -5], 7)
tutte8 = nx.LCF_graph(30, [-13, -9, 7, -7, 9, 13], 5)
pg = pg23_incidence()
for name, G, d in [('heawood', heawood, 3), ('tutte8', tutte8, 3), ('pg23', pg, 4)]:
    G = nx.convert_node_labels_to_integers(G)
    assert nx.is_bipartite(G) and all(deg == d for _, deg in G.degree()), name
    print(name, G.number_of_nodes(), 'girth', nx.girth(G), file=sys.stderr)
    nx.write_graph6(G, f'/Users/dogaozden/AI_Projects/p12-work/{name}.g6', header=False)
