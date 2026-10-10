# Construction ideas that have produced records

- Moore bound: a bipartite graph with max degree d and diameter D has at most 2((d-1)^D - 1)/(d-2) vertices. Records approach it only through structure.
- D = 3: if d-1 is a prime power, the incidence graph of the projective plane PG(2, d-1) meets the bound (lib.projective_plane_incidence). Otherwise start from PG(2, q) with q the largest prime power below d-1, then add vertices and edges using the spare degree. Araujo-Pardo and López got order 2(q^2+q+5), degree q+2, by adding 8 vertices to PG(2,q).
- Voltage lifts: pick a small base multigraph (a few vertices, loops and parallel edges allowed) and a cyclic group Z_m. Give each edge a voltage. The lift (lib.voltage_lift) has base_n * m vertices and inherits degree. Many records come from lifts with 2-6 base vertices, found by searching voltages. Search m and voltages, then keep the largest lift that passes lib.within_diameter.
- Haar graphs (lib.haar_graph) are the simplest lifts: base = two vertices joined by d parallel edges. They are bipartite automatically.
- Generalized polygons give the optimal graphs for D = 4 (generalized quadrangles, 2(q+1)(q^2+1) vertices for d = q+1) and D = 6 (generalized hexagons). The incidence graph of points and lines of the quadrangle W(q) is a good start for D = 4.
- Duplication (Delorme-Farhi): replace each vertex of a good graph by k copies and connect copies with a structured pattern. This multiplies the order while increasing the degree.
- Repair search: start from a large near-valid graph, then remove the vertices involved in the most bad pairs (lib.bad_pairs counts them) or rewire edges until it is valid.
- Bipartiteness comes free if every edge joins an "A" vertex to a "B" vertex: build A and B parts explicitly.
