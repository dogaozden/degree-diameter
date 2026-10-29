# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-29, conics job (session 01QYEEyK1tXuucYMjhpJsysH), rounds conics-r1 and conics-r2

Goal: independent checks of the claims of research/synthetic/CONICS.md (conic frames make the hats self-polar, the
polarity completion, Theorem A as conic pairs, the folding lemma in GQs and hexagons), plus two small searches.
Briefs: research/squads/conics-r1/BRIEF.md, research/squads/conics-r2/BRIEF.md. All cards Haiku, run as subagents.

Round 1 (8 cards):
- c1 self-polarity and fold, prime q = 3..13, every conjugate pair: 67/67 pass.
- c2 the same over GF(9) and GF(25): 96/96 pass.
- c3 explicit polarity completion (Prop. 1.10): 24/24 pass.
- c4 negative controls, every labelled frame at q = 5, 7: exactly the conic frames are self-polar (2,496 frames).
- c5 Theorem A as complementary conic pairs: 412 (q, z) pairs, q = 3..13, all pass; eps = 1 fails (control).
- c6 annealer for self-polar five hats at q = 5, 7 (no changes): see the scoreboard (the SAT run of the main session
  settled q = 5: UNSAT in all orbit cases).
- c7 conic fans in H(q): single-direction fans have at most 36 points at q = 5 (exact), 106 found at q = 7; the D = 7
  records use 72 and 288 pairwise opposite points, so fans do not help at small q.
- c8 pseudo-polarities (q = 4, 8) and unitary polarities (q = 4, 9): 6,828/6,830; the 2 "failures" are the frames with
  ell the absolute line, where the brief wrongly assumed tau != id (with tau = id they are self-polar; checked by the
  main session, conics/pseudo_absline.py).
Kept: everything; the checks went into CONICS.md with their card names.

Round 2 (6 cards):
- c1 zero-change four hats self-polar, fold = Erdos-Renyi graph + 5 vertices: 42/42 pass.
- c2 W(2) (all 36 polarities) and W(8) (one polarity found by random search in the nauty group): clones over the
  Suzuki-Tits ovoid and shadow lines over the absolute spread are self-polar; folds of 20, 25 (q = 2) and 650, 715
  (q = 8) vertices, diameter 3.
- c3 H(3): a polarity found with nauty; 28 absolute points and lines; the one-level doubling on them is self-polar of
  diameter 6 and folds to 392 vertices of diameter 5.
- c4 proofread of Section 1: see the scoreboard and c4/review.md.
- c5 proofread of Sections 0, 2, 3 and the literature facts: confirmed (a), (c)-(i); its three "errors" are one
  terminology mix-up (it read "spread of H(q)" as a partition of the points; in hexagons a spread is q^3+1 pairwise
  opposite lines, as in SYNTHETIC.md). CONICS.md now states the definition explicitly.
- c6 nauty on every four-hat frame at q = 5, 7: a polarity exists iff the frame is harmonic with X_a paired with a
  point of T (cross-ratio -1, 2 or 1/2); equianharmonic frames at q = 7 have no correlation; all harmonic four-hat
  structures are isomorphic.
Kept: all, as computer checks in CONICS.md. What the squads added: independent code for every claim, two corrections
of scope (tau = id on the absolute line; the definition of a hexagon spread), and the sharper nauty statement (c6),
which the main session had only for its own polarity.

Round 3 (8 check workers, remote Haiku sessions, 2026-10-29 03:37 UTC): the all-pairs check of the (16,7) candidate
4,081,072 (research/synthetic/conics/d16D7/), split into 8 source ranges of 510,134. Each worker rebuilds the graph
from research/frontier/sols/d16D7_hex13_typedwhisk_n4081072.sol, checks the edge list's sha256, and runs
research/synthetic/conics/apsp_fast.c on its range. Results: research/synthetic/conics/d16D7/checks/.
Result: all 8 workers rebuilt the same edge list (sha256 350f9e07...) and printed RESULT VALID d=16 D=7 n=4081072 for
their ranges (finished 03:56 to 04:10 UTC; about 18 to 32 minutes per range on 4 cores). Verified from the raw tool
output in each session's transcript, not from the workers' summaries. Kept: the check (d16D7/checks/).


## 2026-10-29, conics-2 job (session 01QYEEyGCo3Ku7yyf5CU35zt), round conics2-r1

Goal: two questions of the brief at small q, where checks take seconds. (A) Can a non-friendly (H -> H) transition be
repaired with more freed points than the mirrored surgery (81 at q = 5)? Scorer: research/squads/conics2-r1/tools/
transcheck.py (exact bitset BFS of the two-level graph). (B) Are there dual segment sets larger than the lines meeting v
plus the exact whiskers, q(q^3+1)? Scorer: tools/dualseg_check.py. Brief: research/squads/conics2-r1/BRIEF.md. All cards
Haiku subagents, about 20 minutes each, on this session's machine.

Cards and best scores:
- c1 (A) larger mirrored sets: 81 (record); no extra mirrored pair fits the record's types; tabu partial ovoids only 56.
- c2 (A) Theorem C sets with copied distance-4 structure / annealing on sigma: 81; under the record sigma the points where
  sigma is a local duality are exactly R; swaps never grow it, random starts reach 0.
- c3 (A) add a point and repair sigma by local search: best 589 pairs still beyond 7 at |R| = 82.
- c4 (A) whole three-level graph with hubs instead of one transition: 81; at K = 82 (one extra freed point, hub graph
  rewired) 864 to 1,188 ordered pairs beyond 7 over 12 extra points, all level-to-level, none involving a hub; local search
  on sigma reached 744. The third level and the hubs repair nothing.
- c5 (A) wildcard, exact SAT at q = 3: too large without symmetry breaking (no result).
- c6 (B) exact: maximum dual segment set of H(2) = 25 (26 UNSAT); q = 3: 112 (ovoid pencils, the bound); q = 4: HiGHS
  found nothing above 260 in 150 s.
- c7 (B) local search from the whisker sets: found that q^2 spread lines carry no whisker and can be added (q = 4: 276,
  q = 5: 655, q = 7: 2,457); exact q = 2 maximum 25 by MaxSAT; no move beyond 276 / 655 in millions of moves.
- c8 (B) annealing over point-disjoint pencil stars: 288 at q = 4 (above 276), 24 at q = 2, 508 at q = 5.
Verified by the main session with the scorers: all dual segment sets above (q = 2: 24, 25; q = 4: 276, 288; q = 5: 655;
q = 7: 2,457), and the A-side record and negative controls.
Kept: c7's observation, which the main session proved for every q (research/synthetic/conics2/README.md, Proposition 1:
the q^2 spread lines with nu = 0 carry no whisker) and used to raise R_L by q^2 in every typed layout ((14,7), (16,7),
(17,7), (19,7), (20,7)); c6/c8's sets as evidence that the enlarged set is maximal but not maximum. Side A: no gain; the
negative results are reported as computer evidence in the README. Next: none for A; for B a pencil-type construction
for large q.
