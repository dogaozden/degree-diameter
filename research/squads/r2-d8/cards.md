# r2-d8 cards (read ../r1-d8/README.md for tools, rules and scoreboard format; scoreboard here: r2-d8/scoreboard.jsonl)

New facts since r1: (i) for odd q the DGQ D=8 value equals |V(X)| + |E(X)| where X is the Z_5 polygon cover of H(q)
(5|GH(q)| vertices, degree q+3, diameter 7): N = 5|GH|(1 + (q+3)/2); equivalently N/5 = 2|GH| + #arcs of an Eulerian
orientation of the H(q) incidence graph. (ii) The undirected line digraph of a random Eulerian orientation has
diameter 10, not 8. (iii) Exact "guaranteed-walk" designs are ruled out by a spectral argument; random lifts fail.
Liftdiam is at research/theorems/d8/liftdiam (fixed version). Rules: THREADS=1, `timeout 900 nice -n 10`, <=1.5 GB,
no git commits, write only in your folder research/squads/r2-d8/<card>/ (and append to the scoreboard).

d1  V+E operation. Search for a degree-preserving local operation on a bipartite graph X (degree D, diameter k) that
    yields a bipartite graph with |V(X)| + |E(X)| vertices, max degree D and diameter k+1. Test on small polygon covers
    first: X = Z_5 cover of PG(2,q) + 2 random matchings (q = 3: degree 6, diameter 4), aiming for diameter 5 on
    |V|+|E| vertices; then the Z_5 cover of H(2) (degree 5) / H(3) (degree 6) aiming for diameter 8. Try several
    rules (vertices = V(X) u E(X); an edge-vertex uv joined to u or v and to some edge-vertices; orientations).
d2  States = out-arcs + 2. Vertex set W = V(I) x {1,2} u A(G), I = incidence graph of H(3), G an Eulerian orientation
    of I; build a degree-<=6 bipartite base on W by a local rule (e.g. arc u->w adjacent to the out-arcs of w, the
    in-arcs of u, and copies of w), then a Z_5 lift with polygon-cover-like voltages; target: diameter 8 on
    5*|W| = 14,560 vertices (degree 6). Score = unreached pairs.
d3  Colour voltages + polygon part (evolves r1/c5, best of round 1). Group Z_5 x Z_k: flags of H(5) coloured by q+1
    perfect matchings, colour c gets (0, v_c); hops get (1, w_1), (2, w_2) (or point-dependent w); hill-climb v, w.
    Target M = 5k >= 15 at q = 5 with unreached 0 (r1 random baseline: 10), stretch 20.
d4  j=1 targeted annealing at q=4: one hop matching, Z_8 (M = q+4 = 8). Anneal voltages (flags and hop) but choose
    moves on edges near currently unreached pairs (use unreached_profile.py or your own BFS). Baseline: a plain
    annealer (research/theorems/d8/lanneal.c) left about 3200 unreached after 20k moves. Report best full count.
d5  Anti-homomorphic hop matching. Find a bijection s: points -> lines of H(3) (then H(4)) such that any two distinct
    non-opposite points (distance <= 4) go to opposite lines (distance 6), or as few violations as possible
    (annealing on the bijection). Then build Z_M lifts (random flag voltages, random hop labels, j=2 using s and a
    second matching) and score the largest M with unreached 0 at q = 3, compared with random matchings (r1: ~14-18).
d6  Literature. Find any publication or report by J. Gomez, C. Delorme or J.-J. Quisquater (1985-2015) describing
    bipartite degree/diameter constructions of diameter 8 from generalized hexagons, or an operation "diameter +1,
    order x (1 + degree/2)" (compound graphs, bipartite line graphs, graphs on alphabets, Kautz-like). Use web search
    and arXiv; quote the statement and give the reference; say "not found" if not found. No contact with anyone.
d7  Wildcard: an approach none of d1-d6, d8 uses. Implement and score it at q = 3 or 5.
d8  The j=1 cell (13,8) = 15|GH(11)| = 3 x 5 copies, Delta = q+2. Test the idea "Z_3 polygon cover x Z_{(q-1)/2} with
    the Z_{(q-1)/2} voltages from GF(q)*/{+-1}" (e.g. a vector-cover: for a flag (p, L) take a coordinate ratio of p
    on L and its class in GF(q)*/{+-1}), at q = 7 (Z_3 x Z_3 = 9 copies, 352,944 vertices) with SRC_STEP 13 first,
    or q = 3, 5 analogues. Score = unreached pairs at diameter 8.
