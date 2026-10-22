# Results ledger for the joint paper (Araujo-Pardo, López, Özden)

Status as of 2026-10-20, 1:45 PM. A full combined build of master is running (lean-buildcheck). One row per result. "Paper proof" = written proof exists in our notes; nobody outside
has read it yet. "Lean" = machine-checked on master with only propext, Classical.choice, Quot.sound.

## AL Problem 4: "generalize the construction to regular bipartite graphs of diameters 4 and 6"

| Result | What it says | Paper proof | Computer check | Lean |
|---|---|---|---|---|
| Hat lemma (Delorme's doubling + Lemma 2) | Doubling a set in a generalized n-gon keeps diameter n iff its pieces are trees of diameter ≤ n−2. Explains AL's hats (n=3: patches needed) and how they generalize (n=4 stars, n=6 radius-2 trees). | research/p4/hats/REPORT.md §1 | random tests | **Yes** (Doubling.condC_iff_forestDiam, delorme_levelled_polygon) |
| Fourth hat, D=3 | 2(q²+q+6), (q+2)-regular, diameter 3, all q ≥ 4; zero-change version keeps the plane intact (research/plus3/plus3.tex, Lean Plus2Zero.zero_isBipartiteDegDiam, q ≥ 3) | research/plus2/coords/coords.tex (projective coordinates, neighbour table) | q=4..13, all (a,c) | **Yes**, regular (Plus2.plus2_regular, any projective plane with a frame) |
| Theorem A, D=4 | AS(q) + two elliptic quadrics: 2q²(q+2), (q+2)-regular, diameter 4, odd q | research/NOTE.md | 1782, 3146, 5070 | **Yes**, regular (ASq.bound_regular) |
| Theorem B / Cor. B1, D=4 | Weighted copies with stand-ins in any GQ; regular versions | research/NOTE.md, research/p4/d4/REPORT.md | many | **Yes** (GQST.standin_*, GQST.regular_copy_graph) |
| Prop. C / Cor. C1, D=4 | Singer 2-ovoids of W(q), all odd q; 5440 at (16,4), regular | research/NOTE.md | 5440 | **Yes** (SingerC.propC, corC1, regular5440) |
| Theorem D, D=6 | H(q) + Delorme levels + q²(q²−1) exact whiskers (explicit rule via spreads S_z and an irreducible cubic): 2(q+1)(q⁴+q²+1) + 2q⁴+4q³+4q+10, max degree q+2, diameter 6, odd q; also m-ary levels (Δ = q+3) | research/p4/hats/REPORT.md §4 (Theorem 4) | q = 5, 7, 9, 11, 13 graphs; key identity now has a hand proof (complex structure J_z, research/geometry/PROOFREAD.md), also checked with sympy | **Yes, odd q** (HexagonD.theorem4 = exact whiskers, theoremD / theoremD_two = the bounds; built on Hexagon.genPolygonGraph_hexagon and Doubling); key identity also separately (HexagonD.Identity); 9592 graph (nb_7_6). Even q: not in Lean |
| Theorem R, D=6 regular | Delete twins + complete: (q+m)-regular, diameter 6, 2(q+1)[q⁴+q²+1+(m−1)(q³+m+1)] vertices, odd q | research/p4/regular/REPORT.md | 9348, 147500, 386328, 866068, 927724 all exactly regular; independent bigcheck VALID on all five (exact diameter 6) | **Yes, odd q** (HexagonD.Regular.theoremR, theoremR_two; paper Thm 6.12) |

**So: is Problem 4 solved?** On paper, yes for odd q: regular graphs at D = 4 (Theorem A, C1) and D = 6 (Theorem R),
beating the table, and the hat lemma says in what sense AL's construction generalizes. Lean now covers Theorem D for odd q. Lean now also covers Theorem R (regular D = 6) for odd q. Not yet: (1) an outside mathematician reading the proofs;
(2) even q in Lean (worked out on paper: research/evenq; the q = 16, 2,384,492-vertex graph passed bigcheck).

## AL Problems 1, 2, Question 1 (local bipartite Moore graphs)
| Result | Status |
|---|---|
| |LBM(3,8)| = 6951; |LBM(4,6)| = 3,747,351; unique closest-to-Moore graph at (4,6); ratio for Q1 at (3,8) | Computer enumeration, validated on AL's (3,6) = 5 and an exact mass formula. research/p12/REPORT.md. Not Lean (enumeration). |

## AL Problem 3 (improve the construction)
Fourth hat: +2 at every q ≥ 4 (above), also with the plane untouched. +3 (research/plus3/plus3.tex): structure theorem (new vertices are near-copies; with no plane changes they form the hat shape); theorem: no +3 with PG(2,q) induced for q ≥ 42; SAT: no +3 in the hat shape with ≤ 3/2/1/1 changes at q = 7/9/11/13; general +3 with plane changes open. n_b(7,3) = 80 is known exact (Feria-Purón et al. 2013).

## Other records (same paper or a second one)
D = 5 Haar graphs (Haar lemma in Lean; 1152, 1764, 2662 kernel-checked); D = 3 (16,3) 396. Not part of AL's problems.

## Prior art to credit
Delorme 1985 (doubling with levels; all old D = 4 and D = 6 table values), Delorme–Farhi 1984, Bamberg–Law–Penttila 2009
(m-ovoids), Tallini 1988, AL 2020 (and the index slip in their printed matching: i ∈ F* fixes it).
