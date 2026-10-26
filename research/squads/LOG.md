# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26, own-d8-compound (Opus, session_01TjGpLmiNHBWJKGjjSCJEKd), round r1_d8c

Goal: a structured compound of copies of I(H(q)) with diameter 8 and degree q+3 that reaches the table's
5*floor((q+5)/2) copies (cells (10,8), (12,8), (14,8), (16,8)); score = largest valid m (exact glift / lifteval /
gcheck) at small q. 16 Haiku cards (model haiku, effort high), about 25 minutes each, all on the 4-core machine
(load peaked at 20, so most cards ran at about 1/5 of a core). Context: research/squads/r1_d8c/CONTEXT.md, cards:
CARDS.md, board: scoreboard.jsonl.

| card | idea | best valid m (q) | note |
|---|---|---|---|
| c1 | pair sheets (2 plain sheets + one per pair of neighbours, permutation lift) | 0 (3, 5) | literal rule disconnected; random sheet maps GCOST 8,878 at m = 20 |
| c2 | flags as vertices (5 x (flags + 2P + 2L)) | 0 (3) | ball growth far too slow; 111 rules |
| c3 | one matching (Delta = q+2) at q = 5 | 0 (5) | random hexagon voltages: cost 5 at m = 5 (zero hexagon voltages: ~1,000) |
| c4 | multiplicative (discrete log) coordinate voltages | 10 (5) | fewer distinct bundle sums than random |
| c5 | duality as the matchings, constant/bilinear voltages | 10 (3) | Z10 lemma only; bilinear best cost 22 at m = 12; built the q = 3 and q = 9 dualities |
| c6 | SAT for bundle-rainbow hexagon voltages (q = 3) | (pending) | |
| c7 | Z10 lemma x Z_k, annealed K-part | 20 (3) | = formula at q = 3; m = 30 cost 744 |
| c8 | typed copies, identity hops | 12 (3) | random Z_m lifts reach 16 at q = 3 |
| c9 | pencil-rainbow line colouring, one matching | 0 (5) | no proper 7-colouring found by tabu (1,374 conflicts) |
| c10 | Hermitian spread voltages | 10 (5) | best structured m = 11 cost 6 |
| c11 | lifting the D7 graph (hexagon-only K-voltages) | (pending) | |
| c12 | hub surgery on the Z10 lemma graph | 10 + 3.8% (3) | 280 hubs (28 orbits) after deleting 90 matching-edge orbits |
| c13 | additive projective parameter with geometric frames | 15 (3) | below random (16) |
| c14 | wildcard: GQ(5,5) base | 500 copies of I(GQ(5)) = 19.97 x I(H(5)) | below 25 |
| c15 | rule search (affine coordinate rules) | 0 (5) | too slow under load |
| c16 | even q (Artin-Schreier) | 14 (4) | random hexagon voltages; trace-structured worse |

Kept: nothing from the cards beats random search. The useful outputs are calibrations (random hexagon voltages: m = 14
at q = 4; one random matching at q = 5 reaches cost 5 at m = 5 once the hexagon is twisted), the surgery gain (+3.8%),
and c5's verified dualities of H(3) and H(9). What Opus did next: from c5's duality files, a new family (the duality
used as both matchings, with pencil-coordinate voltages; research/theorems/D8_COMPOUND.md §4), which reaches all but
0.1-0.2% of targets at q = 9 for m up to 41 but is not valid beyond its strong core; round r2_d8c works on it.
