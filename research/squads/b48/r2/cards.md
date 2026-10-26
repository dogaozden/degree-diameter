# Round 2 cards (26). Read HEADER.md first (it has the round-1 results and the new tools). Folder: research/squads/b48/r2/<card>/

Shorthand: T = /home/user/degree-diameter/research/squads/b48/tools, B = the scratchpad bin dir in HEADER.md.
"abc group" = split abelian-by-cyclic group built by `python3 $T/abc.py build "k p:d,..." G.bin`.
Seed = a valid 2,184-vertex graph in research/squads/b48/seeds/ (haar_meta_91_12_25_*.edges).

## A. Abelian-by-cyclic Haar graphs (the round-1 lead; use haar_tab)

**a01: the order-1,120 lead.** "28 5:4,2:7" (= (Z_5 + F_8) x| Z_28, n = 2,240) reached cost 3 in 20 s. Build every
root-exponent variant "28 5:4@e1,2:7@e2" (e1 in {1,3}, e2 in 1..6), screen each 15 s, then run the best three for
60 s on 2 seeds each. Report the best cost and whether the variants differ at all (some are isomorphic: say which).

**a02: characteristic-2 components.** abc groups with a component over F_{2^f} (F_8 with d = 7, F_16 with d = 5 or
15, F_64 with d = 9, 21 or 63, F_4 with d = 3) plus other components, order 1,094..1,350. List them (write your own
enumeration; abc.py's list skips some), screen 10 s each with haar_tab, push the best two for 60 s.

**a03: Frobenius groups Z_p^m x| Z_d with one irreducible component of dimension m >= 2** (d | p^m - 1, d not dividing
p^j - 1 for j < m): e.g. "24 7:24" (1,176, cost 4 in 20 s: push it hard, 3 seeds x 60 s), "16 3:16" (Z_3^4 x| Z_16,
1,296), "21 2:21" (Z_2^6 x| Z_21, 1,344), "8 13:8" (1,352), "12 11:12" (1,452). Screen all in 1,100..1,460, push the best.

**a04: near-abc: allow d = 1 (central) and d = 2 (inversion) components next to at least one d >= 3 component**,
orders 1,094..1,180 (the cheapest records). abc.py's builder accepts d = 1 and d = 2 ("p:1", "p:2"); its list skips
them, so enumerate yourself. Screen everything with haar_tab 8 s, push the best three for 60 s.

**a05: diagonal (non-scalar) actions on Z_p^2 and Z_p^3.** "4 17:4,17:4@3" (Z_17^2 x| Z_4 by diag(u, u^3), 1,156),
"10 11:10,11:10@3" and "@7" (1,210), "10 11:5,11:10", "6 7:3,7:6" variants, and 3-component diagonal actions
"k p:d@a,p:d@b,p:d@c" with p^3 k in 1,094..1,400 (p = 5, 7). Screen and push the best.

**a06: why the floors?** Z_13^2 x| Z_7 stops at exactly 6 on every seed and Z_55 x|_2 Z_20 at exactly 1. Get near-miss
states with lift (`$T/lift $T/bases/dipole4.txt G.bin 4 8 60 1 8 best.sol`, it saves the best state), list the uncovered
elements (your own BFS), and find their structure: which coset of M, fixed by which automorphism, which word lengths
fail. State a rule that predicts the floor from (k, components) and test it on 3 groups you have not seen.

**a07: three-component abc groups**, orders 1,094..1,300 (e.g. "6 2:3,7:3,7:6" cost 26, "12 2:3,5:4,5:4",
"3 2:3,2:3,5:3", "6 2:3,2:3,13:6"), with @e variants for repeated primes. Screen with haar_tab 8 s, push the best.

**a08: bigger orders 1,250..1,450 (n = 2,500..2,900).** A cost-0 graph here would be a big jump. List abc groups
(abc.py list 1250 1450 --nonmeta, plus metacyclic ones with k >= 12 and gcd(r-1, m) <= 2), screen 10 s, push the best.

**a09: abc groups as voltage groups of 2+2 bases** ($T/bases/b22_t1.txt, b22_t2.txt), group order 547..700
(n = 4N): enumerate abc groups of order 547..700 (`abc.py list 547 700 --nonmeta`, plus metacyclic ones with
ord(r) >= 6), anneal with lift (`$T/lift BASE G.bin 4 8 40 SEED 8 OUT`; 40 s runs). Round 1's best 2+2 lift was cost 10
(miss 2.5) at n = 2,200 with Z_55 x| Z_10.

**a10: single field, non-faithful cyclic part.** G = F_q x| Z_k where Z_k acts through Z_d (d | gcd(k, q - 1)), i.e.
abc.py "k p:d" with d < k (the rest of Z_k is central). Orders 1,094..1,250, q = 8, 9, 16, 25, 27, 32, 49, 64, 81,
121, 125, 128, 169 and primes. Compare with the faithful versions. Screen and push the best.

**a11: annealing settings on the 1,120 and 1,176 leads.** Same groups ("28 5:4,2:7" and "24 7:24"), different search:
K (candidates per move) 4 / 8 / 16, different seeds, haar_tab env knobs (read the header of
/home/user/degree-diameter/research/structured/haar_fast.c and research/frontier/haar_gen3.c for COOL, REHEAT,
RANDSAMPLE etc.), and lift with T0/T1/EPOCH. Report which setting gets lowest, and the best cost.

**a12: exhaustive inner loop on the 1,120 group.** In "28 5:4,2:7" the normal subgroup M = Z_5 + F_8 has only 40
elements and the quotient is Z_28. For S = {e, x, y, z}, fix the Z_28-parts (j-pattern) and enumerate all 40^3 = 64,000
M-parts with `$T/lift $T/bases/dipole4.txt G.bin 4 8 eval` (the index of (m, j) is j*40 + m; check with a known
element). Choose j-patterns from the best annealed states or by a quick sampled score; do as many patterns as your CPU
budget allows. This settles whether a pattern admits cost 0.

## B. Surgery on valid seeds (round 1: n = 2,186 with 247 far pairs, card c31)

**b01: robust seeds.** Get as many different valid 2,184 Haar graphs as you can (haar_fast on meta 91 12 25 with many
seeds, and on the cost-3..5 groups of order 1,092: meta 91 12 6, 182 6 23, 91 12 18, 182 6 3), and for each compute
the damage of deleting one edge per generator orbit (`$T/edgecrit FILE.edges 8 0 4` gives the 4 edges at vertex 0, one
per orbit). The 3 seeds we have all show 180, 180, 165, 165 (maybe isomorphic). Find seeds with smaller damage; save
them as edge lists in your folder and report the smallest damage found.

**b02: choose the 3 deleted edges smartly.** For the seed, compute for each edge the SET of pairs it destroys (pairs
far in G minus that edge; by symmetry only 4 edge orbits, translate with the group action or just recompute), then pick
triples (a_i b_i) whose destroyed sets overlap most / are rescued by the x-y detour, and also make x and y reach
everything (every B-vertex within 6 of some b_i or within 4 of some a_i). Exact check of the best candidates with
score48 (3 ms each). Report the smallest far count at n = 2,186.

**b03: other insertion gadgets.** (i) delete 4 edges a_i b_i, x adjacent to b_1..b_4, y adjacent to a_1..a_4, no x-y;
(ii) delete 2 edges, x adjacent to b_1, b_2, y (degree 3), y adjacent to a_1, a_2, x (degree 3; max degree 4 allows it);
(iii) delete 1 edge and add a path a_1 - y - x - b_1 plus more. Compare best far counts over many random choices plus
local search on the choice.

**b04: repair c31's graph.** /home/user/degree-diameter/research/squads/b48/r1/c31/best_c.edges (n = 2,186, 247 far,
x = 2184, y = 2185). Moves: re-choose one insertion edge (delete a different a_i b_i), 2-switches among edges within
distance 2 of far-pair endpoints, exact evaluation (APSP ~3 ms; write a C evaluator or call score48). Steepest descent
and annealing. Report the smallest far count.

**b05: geometry of good triples.** Sample thousands of random insertion triples on the seed (exact far count each),
and correlate the far count with the distances between the deleted edges, the generator orbits they belong to, etc.
Find the pattern of good triples, then exploit it (search inside the pattern). Report the best far count and the rule.

**b06: slack versus order.** Find valid Haar graphs at smaller orders (N = 1,040..1,091: metacyclic and abc groups with
haar_fast/haar_tab) and measure their edge damage (edgecrit). How fast does the damage fall as N drops? Is there an N
where single-edge deletions are harmless, so that several insertions (to reach n >= 2,186) could work? Try the
insertion surgery on the most robust one you find (several pairs x, y if needed).

**b07: other local gadgets that add 2 vertices.** Replace a small subgraph of the seed (an edge, a vertex with its 4
edges, a 4-path, an 8-cycle) by a gadget with 2 more vertices, max degree 4, bipartite. Enumerate gadget shapes and
placements, exact evaluation. Report the best far count at n = 2,186.

**b08: annealing over insertion choices.** State = (which 3 edges are deleted, which b's x attaches to, which a's y
attaches to), exact far count as energy (APSP ~3 ms), moves = change one choice. Simulated annealing for your whole CPU
budget. Report the best far count at n = 2,186.

**b09: insertion into a lift near miss with the far pairs matched.** The Haar near miss at n = 2,200 (Z_55 x|_2 Z_20,
r1/c01/best_cost1_n2200.edges) has exactly one far partner per vertex (1,100 far pairs, a perfect matching of type
(g, A)-(g u, B)). Deleting vertices cannot help, but a global rewiring might: e.g. replace a whole edge orbit (one
generator) by a different matching chosen to serve the far pairs. Explore rewirings of one generator class (1,100 edges)
with exact evaluation.

## C. Side lines

**c01: escape the 1,100 trap with a margin objective.** Anneal Haar S with cost = uncovered + w * (number of elements
covered by exactly one word), so fragile states are penalised; write your own annealer (C) using a group table. Test on
meta 55 20 2 and on "28 5:4,2:7". Report the best true cost.

**c02: fast 2+2 and 3+3 lifts with flift.** New director tool `$T/flift BASE GROUP 4 8 SECONDS SEED 8 OUT` (same
arguments as lift, ~15x faster: bit-parallel BFS over cosets; voltages act by left multiplication; loops not supported;
writes OUT and OUT.edges, check with score48). Use it on 2+2 bases ($T/bases/b22_t1.txt, b22_t2.txt) and 3+3 bases
($T/bases/k33_matching.txt and the other 3+3 classes from r1/c20) with metacyclic (meta:m:k:r) and abc groups (abc.py
.bin) of order 550..620 (2+2) or 365..420 (3+3). Screen 10 s each, push the best 3 for 60 s. Round 1's best 2+2 lift was
cost 10 (miss 2.5) at n = 2,200 with Z_55 x| Z_10 (meta:55:10:4).

**c03: hard-set first.** For the 1,120 and 1,176 leads ("28 5:4,2:7", "24 7:24"), find the elements that are most
often uncovered over many good S (anneal briefly many times with lift, which saves states; collect the uncovered
elements). Then restrict the search to S that cover the hard set (e.g. exhaust the last generator for each good pair of
first generators with lift eval). Report the best cost.

## D. Wildcards

**w1: wildcard.** Any direction not in A, B, C, and not in round 1's cards (r1/cards.md). Say which in "idea".
**w2: wildcard, analysis first.** Read the round-1 board (r1/scoreboard.jsonl) and a few near-miss files, find what
the best near misses have in common, propose a construction from that, and run it.
