# Candidate record graphs from research/theorems (not Haar graphs, so not in research/frontier/sols)

| file | cell | vertices | table (DS14v2) | how to rebuild and check |
|---|---|---|---|---|
| d16D5_n31460_flagsA4_q3.edges.gz | (16,5) | 31,460 | 27,300 | `python3 ../flags.py 3 OUT.edges` rebuilds the same edge list (sha256 18a9cc6e183b6e644352bd2a73b664f56fe65eebce3eb42f5f038df6d7015528 uncompressed); `apsp OUT.edges 16 5` (research/lifts/coordinator_check/apsp.c) gives VALID, 16-regular, bipartite, diameter 5 |

Format: first line the number of vertices n, then one edge "u v" per line. Odd flags (W1 < W3) of GF(3)^5 are
0..15729, even flags (W2 < W4) are 15730..31459; an edge is a complete flag W1 < W2 < W3 < W4.
The graph is the bipartite compatibility graph C(2,3) of Cames van Batenburg and Korsky (arXiv:2608.03965).
