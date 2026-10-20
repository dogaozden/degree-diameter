# Problems 1 and 2 of Araujo-Pardo & López (arXiv 2005.02427): local bipartite Moore graphs

Night of 2026-10-19/20. Agents: p12-haiku (brute force, nauty), p12b-sonnet (tree completion). Saved by the main session.

## Results
| (Δ,g) | Moore order | \|RB(Δ,g)\| | \|LBM(Δ,g)\| | ratio (Question 1) | closest to Moore (other than the Moore graph) |
|---|---|---|---|---|---|
| (3,6) | 14 | 13 (paper) | **5** (= paper, Prop. 1) | 5/13 | as in the paper |
| (3,8) | 30 | 23,466,857 (paper) | **6,951** | ≈ 2.96·10⁻⁴ | see lbm46/an38.txt |
| (4,6) | 26 | ≈ 10¹⁰ (not enumerated) | **3,747,351** | — | unique 6^14 4^12 graph = the 2-switch of PG(2,3) |

**Problem 1 (enumeration):** |LBM(3,8)| = 6951 and |LBM(4,6)| = 3,747,351, up to isomorphism. The Moore graphs are in the
lists: Tutte's 8-cage (8^30, |Aut| = 1440, 45 Moore edges) and the incidence graph of PG(2,3) (6^26, |Aut| = 11232,
52 Moore edges; the only graph with that girth vector).

**Problem 2 (closest to Moore), (4,6):** local girths are only 4 or 6, so the girth norm is 2 × (number of vertices of
local girth 4) and the lexicographic N_p ranking agrees with it. 12 girth-vector classes:
| class | N1 | graphs |
|---|---|---|
| 6^26 | 0 | 1 (PG(2,3)) |
| 6^14 4^12 | 24 | 1 |
| 6^11 4^15 | 30 | 1 |
| 6^10 4^16 | 32 | 6 |
| 6^9 4^17 | 34 | 6 |
| 6^8 4^18 | 36 | 28 |
| 6^7 4^19 | 38 | 70 |
| 6^6 4^20 | 40 | 433 |
| 6^5 4^21 | 42 | 2,169 |
| 6^4 4^22 | 44 | 19,291 |
| 6^3 4^23 | 46 | 260,299 |
| 6^2 4^24 | 48 | 3,465,046 |
The classes 6^13 4^13 and 6^12 4^14 are empty. The closest non-Moore graph is unique: 6^14 4^12, |Aut| = 16, 18 Moore
edges, and it is the single 2-switch of PG(2,3) (all 702 possible switches give this graph). graph6:
Ys_?????????????GwA@WPK?_R?gK?WQ?aD?GQ_?co?@I_?CWO?Ag_??
Next: 6^11 4^15 (|Aut| 72, 10 Moore edges): Ys_?????????????GwA?qOH_Oh?Ok@B_?aI?H@O?QQ?AGo?Dc??Bg???
The six 6^10 4^16 graphs are in lbm46/closest.tsv.

## Method
Every G in LBM(Δ,g) is the bipartite Moore tree hung from an edge uv plus a (Δ−1)-regular bipartite graph H between
the two leaf sets. For (4,6): H is 3-regular bipartite on 9+9 vertices (224 graphs with classes distinguished, generated
by genbg, disconnected allowed); for each H, every way to hang the leaves under the tree up to the tree's symmetry (280
partitions per side, 78,400 per H, 17.6M graphs in all); nauty canonical forms; dedupe.
**Validation.**
1. (3,6) gives exactly the paper's 5 graphs and girth vectors.
2. Mass formula (independent completeness check): Σ over graphs of 2·E_M·|Aut(T)|/|Aut G| must equal the number of
   labelled 0/1 matrices with line sums Δ−1. It holds exactly: 90 for (3,6); 187,530,840 for (3,8);
   12,025,780,892,160 for (4,6) (recomputed by DP).
3. Moore graphs present; every graph has ≥ 1 Moore edge.
4. Brute force for (3,8) (genbg 15+15 | labelg | filter) reproduced (3,6) first; the full (3,8) run moved to 4 cloud
   shards (branches p12-bf-0..3) as an independent check of 6951.

## Feasibility
(3,10) (62 vertices) and (5,6) (42 vertices) are far beyond brute force; tree completion there means (Δ−1)-regular
bipartite completions on 16+16 resp. 16+16 leaves up to a much larger tree group — possibly feasible for (5,6) with more
work, not attempted.

## Files
lbm46/tc.c (generator), an.c (analysis), mass.py; closest.tsv; summary46.txt; u38.g6/o38.tsv/an38.txt ((3,8));
u46.g6 (all 3,747,351 graphs, 214 MB, kept locally, not in git; sha256 474624b046f0b175993503e39c4de132f5727bb47bf6f4bcfc722b95f89675fc) and g46.tsv (per-graph data, local).
