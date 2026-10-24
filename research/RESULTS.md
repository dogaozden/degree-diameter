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

- Oct 22 23:12 PT (harvest): (7,10) 2,147,040 (was 2,125,440), sl 71 n 3; w3-d7D10w4.
- Oct 22 23:12 PT (harvest): (9,9) 3,290,112 (was 3,188,160), prod sl 7 sl 17 n 1; w3-d9D9w1.
- Oct 22 23:12 PT (harvest): (13,8) 6,408,480 (was 6,223,104), psl 79 n 13; w3-d13D8w2.

- Oct 23 00:42 PT (harvest): (8,7) 41,040 (was 40,586), sl 19 n 3; master.
- Oct 23 00:42 PT (harvest): (10,10) 57,868,272 (was 50,331,156), sl 307 n 1; master.
- Oct 23 00:42 PT (harvest): (12,9) 32,772,096 (was 30,001,152), sl 127 n 8; master.
- Oct 23 00:42 PT (harvest): (12,10) 310,628,640 (was 300,383,050), sl 281 n 7; master.
- Oct 23 00:42 PT (harvest): (13,9) 62,156,160 (was 50,990,610), sl 109 n 24; master.
- Oct 23 00:42 PT (harvest): (14,9) 111,482,880 (was 95,087,738), sl 191 n 8; master.
- Oct 23 00:42 PT (harvest): (15,8) 16,483,200 (was 14,172,480), sl 101 n 8; master.
- Oct 23 00:42 PT (harvest): (15,9) 190,887,072 (was 168,016,334), sl 457 n 1; master.
- Oct 23 00:42 PT (harvest): (16,9) 316,679,760 (was 288,939,118), sl 541 n 1; master.

- Oct 23 02:18 PT (harvest): (6,7) 8,370 (was 8,310), meta 279 15 7 n 1; master.
- Oct 23 02:18 PT (harvest): (13,10) 636,550,992 (was 617,330,936), sl 307 n 11; master.
- Oct 23 02:18 PT (harvest): (14,10) 1,217,130,096 (was 1,213,477,190), sl 443 n 7; master.

- Oct 23 11:13 PT (harvest): (6,7) 8,440 (was 8,370), meta 844 5 477 n 1; w4-d6D7_w1.
- Oct 23 11:13 PT (harvest): (7,8) 95,760 (was 88,920), psl 19 n 14; claude/structured-haar-search-ws7bet.
- Oct 23 11:13 PT (harvest): (8,7) 43,344 (was 41,040), sl 8 poly x^3+x+1 n 43; claude/structured-haar-search-ws7bet.
- Oct 23 11:13 PT (harvest): (8,8) 239,904 (was 225,792), psl 17 n 49; claude/structured-haar-search-ws7bet.

- Oct 23 11:19 PT (harvest): (7,9) 449,328 (was 416,640), psl 23 n 37; claude/structured-haar-search-ws7bet.

- Oct 23 12:11 PT (harvest): (7,9) 462,840 (was 449,328), psl 29 n 19; claude/structured-haar-search-ws7bet.
- Oct 23 12:11 PT (harvest): (8,9) 1,316,016 (was 1,245,312), sl 37 n 13; claude/structured-haar-search-ws7bet.
- Oct 23 12:11 PT (harvest): (9,8) 511,056 (was 497,904), sl 27 poly x^3+2x+1 n 13; claude/structured-haar-search-ws7bet.

- Oct 23 13:11 PT (harvest): (8,10) 7,802,160 (was 7,349,616), sl 59 n 19; claude/structured-haar-search-ws7bet.
- Oct 23 13:11 PT (harvest): (10,9) 8,003,856 (was 7,488,000), sl 83 n 7; claude/structured-haar-search-ws7bet.
- Oct 23 13:11 PT (harvest): (13,8) 6,604,416 (was 6,408,480), prod sl 8 poly x^3+x+1 sl 8 poly x^3+x+1 n 13; claude/structured-haar-search-ws7bet.

- Oct 23 14:11 PT (harvest): (7,10) 2,234,400 (was 2,147,040), psl 49 poly x^2+1 n 19; claude/structured-haar-search-ws7bet.
- Oct 23 14:11 PT (harvest): (11,9) 16,792,080 (was 16,369,920), sl 61 n 37; claude/structured-haar-search-ws7bet.

- Oct 23 14:12 PT (harvest): (10,10) 58,863,480 (was 57,868,272), psl 389 n 1; claude/structured-haar-search-ws7bet.

- Oct 23 15:11 PT (harvest): (6,7) 8,880 (was 8,440), sl 5 n 37; claude/structured-search-orbit-w5dd4f.
- Oct 23 15:11 PT (harvest): (6,9) 127,296 (was 121,440), sl 17 n 13; claude/structured-search-orbit-w5dd4f.
- Oct 23 15:11 PT (harvest): (6,10) 524,160 (was 506,160), prod sl 5 psl 7 n 13; claude/structured-search-orbit-w5dd4f.
- Oct 23 15:11 PT (harvest): (9,8) 540,360 (was 511,056), psl 19 n 79; claude/structured-search-orbit-w5dd4f.
- Oct 23 15:11 PT (harvest): (10,10) 60,141,120 (was 58,863,480), sl 79 n 61; claude/structured-haar-search-ws7bet.
- Oct 23 15:11 PT (harvest): (13,9) 63,872,400 (was 62,156,160), sl 101 n 31; claude/structured-haar-search-ws7bet.
- Oct 23 15:11 PT (harvest): (14,9) 116,068,656 (was 111,482,880), sl 67 n 193; claude/structured-haar-search-ws7bet.
- Oct 23 15:11 PT (harvest): (16,9) 324,164,400 (was 316,679,760), sl 149 n 49; claude/structured-haar-search-ws7bet.

- Oct 23 15:20 PT (coordinator): (3,8) 288 (was 256), (5,9) 28,560 (was 27,936), (5,10) 93,000 (was 90,068): voltage-lifts session finds, rebuilt and checked all-pairs by the coordinator (research/lifts/coordinator_check/).

- Oct 23 17:11 PT (harvest): (9,9) 3,407,040 (was 3,290,112), prod sl 5 psl 13 n 13; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:11 PT (harvest): (9,10) 23,142,048 (was 22,178,688), psl 47 n 223; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:11 PT (harvest): (11,8) 2,258,520 (was 2,246,940), psl 59 n 11; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:11 PT (harvest): (12,9) 33,948,672 (was 32,772,096), sl 257 n 1; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:11 PT (harvest): (12,10) 325,832,976 (was 310,628,640), sl 107 n 133; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:11 PT (harvest): (13,10) 667,903,200 (was 636,550,992), sl 151 n 97; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:11 PT (harvest): (14,10) 1,292,644,080 (was 1,217,130,096), sl 181 n 109; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:11 PT (harvest): (15,8) 17,998,512 (was 16,483,200), psl 137 n 7; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:11 PT (harvest): (15,9) 205,083,600 (was 190,887,072), sl 149 n 31; claude/structured-search-orbit-w5dd4f.
- Oct 23 17:25 PT (coordinator): (5,10) 93,444 (was our 93,000): Haar graph of Z1797 ⋊₂₁₂ Z26, voltage-lifts session; rebuilt and checked all-pairs (research/lifts/coordinator_check/check_2026-10-23b.txt).
- Oct 23 18:20 PT (coordinator): (5,10) 95,472 (was our 93,444): Haar graph of Z1989 ⋊₄₆₁ Z24, voltage-lifts session; rebuilt and checked all-pairs (research/lifts/coordinator_check/check_2026-10-23c.txt).

- Oct 23 19:11 PT (harvest): (9,9) 3,443,328 (was 3,407,040), prod psl 7 psl 7 n 61; claude/structured-search-orbit-w5dd4f.
- Oct 23 19:11 PT (harvest): (13,8) 6,814,080 (was 6,604,416), sl 64 poly x^6+x+1 n 13; claude/cd-theory-beyond-random-3ybyf2.
- Oct 23 19:11 PT (harvest): (14,10) 1,308,373,248 (was 1,292,644,080), sl 193 n 91; claude/structured-search-orbit-w5dd4f.
- Oct 23 19:12 PT (coordinator): (4,10) 12,246 (was 11,748, new cell): Haar graph of the metacyclic group Z157 ⋊₉ Z39 with S = {(0,0), (151,25), (63,2), (38,5)}; voltage-lifts session; rebuilt and checked all-pairs (research/lifts/coordinator_check/check_2026-10-23d.txt).

- Oct 23 20:11 PT (harvest): (9,9) 3,499,776 (was 3,443,328), prod psl 7 sl 7 n 31; claude/structured-search-orbit-w5dd4f.
- Oct 23 20:11 PT (harvest): (15,8) 18,128,880 (was 17,998,512), sl 109 n 7; claude/structured-search-orbit-w5dd4f.
- Oct 23 20:11 PT (harvest): (15,9) 208,029,120 (was 205,083,600), sl 79 n 211; claude/structured-search-orbit-w5dd4f.
- Oct 23 20:11 PT (coordinator): (5,8) 9,576 (was 9,234, new cell): Haar graph of the metacyclic group Z266 ⋊₁₇ Z18 with S = {(0,0), (51,5), (129,13), (156,5), (110,11)}; voltage-lifts session; rebuilt and checked all-pairs (research/lifts/coordinator_check/check_2026-10-23e.txt).
- Oct 23 20:25 PT (coordinator): (16,5) 31,460 (new cell, table 27,300): bipartite flag graph of PG(4,3) (Cames van Batenburg–Korsky, arXiv:2608.03965), noticed by the theorem-search session (claude/theorem-search-regularities-nt0d98); rebuilt from the definition and checked all-pairs (research/theorems/coordinator_check/).
- Oct 23 20:45 PT (coordinator): correction: (16,5) 31,460 is a published graph (CvB–K 2026), so it does not count as ours; it is now the value to beat.

- Oct 23 20:47 PT (harvest): (13,10) 677,714,400 (was 667,903,200), sl 199 n 43; claude/structured-search-orbit-w5dd4f.

- Oct 23 22:11 PT (harvest): (6,8) 31,680 (was 30,576), psl 11 n 24; claude/degree-diameter-table-squad-0xgp3g.
- Oct 23 22:11 PT (harvest): (12,9) 34,026,720 (was 33,948,672), sl 41 n 247; claude/structured-search-orbit-w5dd4f.
- Oct 23 22:11 PT (harvest): (13,9) 67,742,688 (was 63,872,400), sl 103 n 31; claude/structured-search-orbit-04hefm.
- Oct 23 22:12 PT (coordinator): (5,7) 3,120 (was 3,110, new cell): Haar graph of PGL(2,5) × Z13 (research/lifts/sols/haar/hc_d5D7_pgl_5_13_s1.txt); voltage-lifts session; rebuilt and checked all-pairs (research/lifts/coordinator_check/check_2026-10-23f.txt).

- Oct 23 23:11 PT (harvest): (9,10) 23,725,584 (was 23,142,048), psl 73 n 61; claude/structured-search-orbit-w5dd4f.
- Oct 23 23:11 PT (harvest): (14,10) 1,316,504,400 (was 1,308,373,248), sl 149 n 199; claude/structured-search-orbit-w5dd4f.

- Oct 24 00:11 PT (harvest): (7,10) 2,237,760 (was 2,234,400), prod psl 5 sl 8 poly x^3+x+1 n 37; claude/degree-diameter-table-squad-0xgp3g.
- Oct 24 00:11 PT (harvest): (8,9) 1,320,120 (was 1,316,016), psl 19 n 193; claude/degree-diameter-table-squad-0xgp3g.
- Oct 24 00:11 PT (harvest): (8,10) 7,818,096 (was 7,802,160), sl 67 n 13; claude/degree-diameter-table-squad-0xgp3g.
- Oct 24 00:11 PT (harvest): (9,10) 23,975,280 (was 23,725,584), psl 71 n 67; claude/structured-search-orbit-w5dd4f.
- Oct 24 00:11 PT (harvest): (14,10) 1,326,627,120 (was 1,316,504,400), sl 139 n 247; claude/structured-search-orbit-w5dd4f.
- Oct 24 00:11 PT (harvest): (16,9) 337,394,400 (was 324,164,400), sl 151 n 49; claude/structured-search-orbit-w5dd4f.
- Oct 24 00:20 PT (coordinator): (16,5) 33,792 (table 27,300; beats the published PG(4,3) flag graph 31,460 and the 32,768 double cover of the LANL (16,4) graph): our own construction, a route-chart lift of K3,3 + perfect matching over Z22 with fibre F4^4, by the beat-16-5-squad session (the chart came from squad round 2, card 5). Checked all-pairs by the coordinator (research/theorems/coordinator_check/check_d16D5_33792.txt).
- Oct 24 00:13 PT (coordinator): (4,10) 12,416 (was 12,246, raised): Haar graph of the metacyclic group Z97 ⋊₁₉ Z64 with S = {(0,0), (74,51), (30,20), (47,1)}; voltage-lifts session; rebuilt and checked all-pairs (research/lifts/coordinator_check/check_2026-10-24a.txt).

- Oct 24 09:55 PT (harvest): (8,9) 1,323,696 (was 1,320,120), psl 23 n 109; claude/degree-diameter-table-squad-0xgp3g.

- Oct 24 10:11 PT (harvest): (8,9) 1,326,960 (was 1,323,696), sl 19 n 97; claude/degree-diameter-table-squad-0xgp3g.
- Oct 24 11:25 PT (coordinator): (7,7) 23,462, (9,7) 117,650, (11,7) 398,582: the generalized-hexagon construction X(M) of the table (3·|H(q)|, Δ = q+2) plus hub vertices, by the exp2-squad session (squad experiment 2, arm B). The solo arm got (7,7) 23,438. All checked all-pairs by the coordinator (research/squads/exp2/coordinator_check/check_d7_hex.txt).
- Oct 24 12:15 PT (coordinator): new cells (4,7) 864 (two vertex-transitive graphs, thm-smallfamilies), (12,5) 8,748 and (15,5) 20,736 (route-chart lifts, thm-chartlift); raised (8,5) 2,048 (chart lift), (7,7) 23,484 and (11,7) 398,606 (exp2-squad, hexagon + hubs). All checked all-pairs by the coordinator (research/coordinator_check/check_2026-10-24_noon.txt).

- Oct 24 14:55 PT (harvest): (13,8) 6,999,552 (was 6,814,080), prod sl 7 sl 7 n 31; claude/thm-order2-symmetry-gap-4e2nmi.
- Oct 24 15:05 PT (coordinator): raised (7,7) 23,488 and (9,7) 117,690 (exp2-squad, hexagon + hubs); (13,8) 6,999,552 (thm-order2, cloud-checked). Squad experiment 2 final: arm B 2.54 units, all three cells beaten with the larger margins; arm A 2.86 units, all three beaten (23,468, 117,656, 398,582); arm C none.
