# Results ledger for the joint paper (Araujo-Pardo, López, Özden)

Status as of 2026-10-22, 2:30 AM PT. One row per result. "Paper proof" = written proof exists in our notes; nobody outside
has read it yet. "Lean" = machine-checked on master with only propext, Classical.choice, Quot.sound.

## AL Problem 4: "generalize the construction to regular bipartite graphs of diameters 4 and 6"

| Result | What it says | Paper proof | Computer check | Lean |
|---|---|---|---|---|
| Hat lemma (Delorme's doubling + Lemma 2) | Doubling a set in a generalized n-gon keeps diameter n iff its pieces are trees of diameter ≤ n−2. Explains AL's hats (n=3: patches needed) and how they generalize (n=4 stars, n=6 radius-2 trees). | research/p4/hats/REPORT.md §1 | random tests | **Yes** (Doubling.condC_iff_forestDiam, delorme_levelled_polygon) |
| Fourth hat, D=3 | 2(q²+q+6), (q+2)-regular, diameter 3, all q ≥ 4; zero-change version keeps the plane intact (research/plus3/plus3.tex, Lean Plus2Zero.zero_isBipartiteDegDiam, q ≥ 3) | research/plus2/coords/coords.tex (projective coordinates, neighbour table) | q=4..13, all (a,c) | **Yes**, regular (Plus2.plus2_regular, any projective plane with a frame) |
| Theorem A, D=4 | AS(q) + two elliptic quadrics: 2q²(q+2), (q+2)-regular, diameter 4, odd q | research/NOTE.md | 1782, 3146, 5070 | **Yes**, regular (ASq.bound_regular) |
| Theorem B / Cor. B1, D=4 | Weighted copies with stand-ins in any GQ; regular versions | research/NOTE.md, research/p4/d4/REPORT.md | many | **Yes** (GQST.standin_*, GQST.regular_copy_graph) |
| Prop. C / Cor. C1, D=4 | Singer 2-ovoids of W(q), all odd q; 5440 at (16,4), regular | research/NOTE.md | 5440 | **Yes** (SingerC.propC, corC1, regular5440) |
| Theorem D, D=6 | H(q) + Delorme levels + q²(q²−1) exact whiskers (explicit rule via spreads S_z and an irreducible cubic): 2(q+1)(q⁴+q²+1) + 2q⁴+4q³+4q+10, max degree q+2, diameter 6, odd q; also m-ary levels (Δ = q+3) | research/p4/hats/REPORT.md §4 (Theorem 4) | q = 5, 7, 9, 11, 13 graphs; key identity now has a hand proof (complex structure J_z, research/geometry/PROOFREAD.md), also checked with sympy | **Yes, odd q** (HexagonD.theorem4 = exact whiskers, theoremD / theoremD_two = the bounds; built on Hexagon.genPolygonGraph_hexagon and Doubling); key identity also separately (HexagonD.Identity); 9592 graph (nb_7_6). **Even q ≥ 4: Yes** (HexagonEven.genPolygonGraph_hexagon_even, theorem4_even, theoremD_even; Oct 22); **q = 2: Yes** (HexagonEven.theoremD_q2, explicit 12-whisker set, exactness q2_exact) |
| Theorem R, D=6 regular | Delete twins + complete: (q+m)-regular, diameter 6, 2(q+1)[q⁴+q²+1+(m−1)(q³+m+1)] vertices, odd q | research/p4/regular/REPORT.md | 9348, 147500, 386328, 866068, 927724 all exactly regular; independent bigcheck VALID on all five (exact diameter 6) | **Yes, odd q** (HexagonD.Regular.theoremR, theoremR_two; paper Thm 6.12); **even q ≥ 4: Yes** (HexagonEven.theoremR, theoremR_two); **q = 2: Yes** (HexagonEven.theoremR_q2, 192 vertices, 4-regular) |

**So: is Problem 4 solved?** On paper, yes for odd q: regular graphs at D = 4 (Theorem A, C1) and D = 6 (Theorem R),
beating the table, and the hat lemma says in what sense AL's construction generalizes. Lean now covers Theorem D for odd q. Lean now also covers Theorem R (regular D = 6) for odd q. Not yet: (1) an outside mathematician reading the proofs;
(2) nothing else: Lean now covers every prime power q at D = 6 (odd q, even q ≥ 4 by the formula, q = 2 by an explicit computer-found whisker set; Oct 22). Full library build and all axioms files regenerated identical in the cloud, Oct 22.

## AL Problems 1, 2, Question 1 (local bipartite Moore graphs)
| Result | Status |
|---|---|
| |LBM(3,8)| = 6951; |LBM(4,6)| = 3,747,351; unique closest-to-Moore graph at (4,6); ratio for Q1 at (3,8) | Computer enumeration, validated on AL's (3,6) = 5 and an exact mass formula. research/p12/REPORT.md. Not Lean (enumeration). |

## AL Problem 3 (improve the construction)
Fourth hat: +2 at every q ≥ 4 (above), also with the plane untouched. +3 (research/plus3/plus3.tex): structure theorem (new vertices are near-copies; with no plane changes they form the hat shape); theorem: no +3 with PG(2,q) induced for q ≥ 42; SAT: no +3 in the hat shape with ≤ 3/2/1/1 changes at q = 7/9/11/13; general +3 with plane changes open. n_b(7,3) = 80 is known exact (Feria-Purón et al. 2013).

## Other records (same paper or a second one)
D = 5 Haar graphs (Haar lemma in Lean; 1152, 1764, 2662 kernel-checked); D = 3 (16,3) 396. Not part of AL's problems.
Oct 22 (frontier-opus, Haar graphs at even D, one covering condition with words of length ≤ D−1): (7,8) 82,992 (table 80,940),
(8,8) 206,448 (201,480), (9,8) 453,840 (449,480), (6,10) 461,472 (452,032). bigcheck VALID twice (agent, coordinator). Table
values from the 2013 Miller–Širáň survey; the live wiki was not readable, so check for newer entries. Not in Lean yet.
Also Oct 22: (8,9) 1,092,960 (table 1,091,232), Haar graph of SL(2,23) × Z45 (odd D); bigcheck VALID twice (agent; coordinator
on an independent rebuild, same sha256, research/frontier/runs/coordinator_check_d8D9_1092960.txt).

## Prior art to credit
Delorme 1985 (doubling with levels; all old D = 4 and D = 6 table values), Delorme–Farhi 1984, Bamberg–Law–Penttila 2009
(m-ovoids), Tallini 1988, AL 2020 (and the index slip in their printed matching: i ∈ F* fixes it).

Oct 23 (frontier watchers: Haiku cloud sessions running haar_gen on 4 cores each; each graph rebuilt independently
by the coordinator with build_haar.py, two BFS from both sides, ecc ≤ D, nothing unreached; runs/coordinator_check_watchers_2026-10-23.txt):
- (7,10) 1,993,920 (table 1,987,380), PSL(2,31) × Z67. New cell past the table.
- (8,9) 1,130,880 (was ours 1,092,960; table 1,091,232), PSL(2,31) × Z38.
- (9,8) 465,120 (was ours 453,840), SL(2,19) × Z34.
- (6,10) 462,840 (was ours 461,472), PSL(2,29) × Z19.
- (8,8) 208,320 (was ours 206,448), PSL(2,31) × Z7.
- (7,8) 83,232 (was ours 82,992), PSL(2,17) × Z17.
- Later Oct 23 (same check): (7,9) 404,928 (table 400,160), SL(2,37) × Z4, new cell; (7,10) → 1,997,520, PSL(2,29) × Z82; (9,8) → 473,616, PSL(2,23) × Z39; (8,8) → 210,528, PSL(2,17) × Z43.

- Oct 22 21:07 PT (harvest): (6,8) 30,576 (was 29,790), sl 13 n 7; watch-d6D8w1-auto.
- Oct 22 21:07 PT (harvest): (6,9) 117,504 (was 117,360), sl 17 n 12; master.
- Oct 22 21:07 PT (harvest): (6,10) 491,400 (was 462,840), psl 27 poly x^3+2x+1 n 25; master.
- Oct 22 21:07 PT (harvest): (7,8) 88,128 (was 83,232), psl 17 n 18; watch-d7D8w1-auto.
- Oct 22 21:07 PT (harvest): (7,9) 416,640 (was 404,928), sl 31 n 7; master.
- Oct 22 21:07 PT (harvest): (7,10) 2,116,800 (was 1,997,520), sl 49 poly x^2+1 n 9; master.
- Oct 22 21:07 PT (harvest): (8,8) 219,240 (was 210,528), psl 29 n 9; master.
- Oct 22 21:07 PT (harvest): (8,9) 1,231,920 (was 1,130,880), sl 59 n 3; master.
- Oct 22 21:07 PT (harvest): (8,10) 7,349,616 (was 6,927,210), sl 107 n 3; master.
- Oct 22 21:07 PT (harvest): (9,8) 487,200 (was 473,616), psl 29 n 20; watch-d9D8w1-auto.
- Oct 22 21:07 PT (harvest): (9,9) 3,188,160 (was 2,961,536), sl 81 poly x^4+x+2 n 3; master.
- Oct 22 21:07 PT (harvest): (9,10) 21,385,728 (was 20,017,260), prod sl 13 sl 17 n 1; master.
- Oct 22 21:07 PT (harvest): (10,9) 7,488,000 (was 7,057,400), prod psl 5 sl 25 poly x^2+2 n 4; master.
- Oct 22 21:07 PT (harvest): (13,8) 6,209,280 (was 5,314,680), prod sl 7 sl 11 n 7; master.

- Oct 22 21:16 PT (harvest): (9,10) 22,178,688 (was 21,385,728), sl 223 n 1; master.
- Oct 22 21:16 PT (harvest): (11,9) 16,369,920 (was 15,200,448), prod sl 7 sl 29 n 1; master.

- Oct 22 21:50 PT (harvest): (6,9) 121,440 (was 117,504), sl 23 n 5; master.
- Oct 22 21:50 PT (harvest): (6,10) 506,160 (was 491,400), pgl 37 n 5; master.
- Oct 22 21:50 PT (harvest): (7,10) 2,125,440 (was 2,116,800), sl 81 poly x^4+x+2 n 2; w3-d7D10w4.
- Oct 22 21:50 PT (harvest): (8,8) 225,792 (was 219,240), prod psl 7 sl 7 n 2; master.
- Oct 22 21:50 PT (harvest): (8,9) 1,245,312 (was 1,231,920), sl 47 n 6; w3-d8D9w1.
- Oct 22 21:50 PT (harvest): (9,8) 497,904 (was 487,200), psl 23 n 41; master.
- Oct 22 21:50 PT (harvest): (13,8) 6,223,104 (was 6,209,280), sl 73 n 8; w3-d13D8w1.

- Oct 22 22:11 PT (harvest): (7,8) 88,920 (was 88,128), psl 19 n 13; w3-d7D8w2.
