Idea (a12): unstructured cubic bipartite graphs, no group. Start from a circulant cubic bipartite graph on n vertices (sides
A = 0..n/2-1, B = n/2..n-1), randomize with bipartiteness-preserving 2-switches (replace a1b1, a2b2 by a1b2, a2b1), and anneal
the number of ordered vertex pairs at distance > 12. Cost is evaluated exactly per move by bit-parallel ball growth
(R_k[v] = R_{k-1}[v] OR over neighbours; 12 rounds on n-bit bitsets, a few ms at n = 2400). Targets n = 2370..2600, the
first n that reaches cost 0 beats 2,368. Not a Haar, Cayley or lift construction, so none of the ruled-out families apply.
