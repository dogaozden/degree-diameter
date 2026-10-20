# Results ledger for the joint paper (Araujo-Pardo, López, Özden)

Status as of 2026-10-20, 9 AM. One row per result. "Paper proof" = written proof exists in our notes; nobody outside
has read it yet. "Lean" = machine-checked on master with only propext, Classical.choice, Quot.sound.

## AL Problem 4: "generalize the construction to regular bipartite graphs of diameters 4 and 6"

| Result | What it says | Paper proof | Computer check | Lean |
|---|---|---|---|---|
| Hat lemma (Delorme's doubling + Lemma 2) | Doubling a set in a generalized n-gon keeps diameter n iff its pieces are trees of diameter ≤ n−2. Explains AL's hats (n=3: patches needed) and how they generalize (n=4 stars, n=6 radius-2 trees). | research/p4/hats/REPORT.md §1 | random tests | **Yes** (Doubling.condC_iff_forestDiam, delorme_levelled_polygon) |
| Fourth hat, D=3 | 2(q²+q+6), (q+2)-regular, diameter 3, all q ≥ 4 | research/plus2/coords/coords.tex (projective coordinates, neighbour table) | q=4..13, all (a,c) | Max-degree version yes (Plus2.plus2, any projective plane); **regular version: running** (lean-regularity) |
| Theorem A, D=4 | AS(q) + two elliptic quadrics: 2q²(q+2), (q+2)-regular, diameter 4, odd q | research/NOTE.md | 1782, 3146, 5070 | Max-degree version yes (ASq.bound); **regularity: running** |
| Theorem B / Cor. B1, D=4 | Weighted copies with stand-ins in any GQ; regular versions | research/NOTE.md, research/p4/d4/REPORT.md | many | **Yes** (GQST.standin_*, GQST.regular_copy_graph) |
| Prop. C / Cor. C1, D=4 | Singer 2-ovoids of W(q), all odd q; 5440 at (16,4), regular | research/NOTE.md | 5440 | **Yes** (SingerC.propC, corC1, regular5440) |
| Theorem D, D=6 | H(q) + Delorme levels + q²(q²−1) exact whiskers (explicit rule via spreads S_z and an irreducible cubic): 2(q+1)(q⁴+q²+1) + 2q⁴+4q³+4q+10, max degree q+2, diameter 6, odd q; also m-ary levels (Δ = q+3) | research/p4/hats/REPORT.md §4 (Theorem 4) | q = 5, 7, 9, 11, 13 graphs; symbolic identities checked with sympy | Doubling part yes; **hexagon H(q) part: started** (lean-hexagon); 9592 graph: running |
| Theorem R, D=6 regular | Delete twins + complete: (q+m)-regular, diameter 6, 2(q+1)[q⁴+q²+1+(m−1)(q³+m+1)] vertices, odd q | research/p4/regular/REPORT.md | 9348, 147500, 386328, 866068, 927724 all exactly regular; independent bigcheck VALID on all five (exact diameter 6) | **abstract part: running** (lean-regularity); needs Theorem D |

**So: is Problem 4 solved?** On paper, yes for odd q: regular graphs at D = 4 (Theorem A, C1) and D = 6 (Theorem R),
beating the table, and the hat lemma says in what sense AL's construction generalizes. Not yet: (1) an outside
mathematician reading the D = 6 proofs; (2) Lean for the hexagon geometry and the whisker rule (the hard part);
(3) even q is not covered at D = 4 (Theorem A) or D = 6 (Theorem D).

## AL Problems 1, 2, Question 1 (local bipartite Moore graphs)
| Result | Status |
|---|---|
| |LBM(3,8)| = 6951; |LBM(4,6)| = 3,747,351; unique closest-to-Moore graph at (4,6); ratio for Q1 at (3,8) | Computer enumeration, validated on AL's (3,6) = 5 and an exact mass formula. research/p12/REPORT.md. Not Lean (enumeration). |

## AL Problem 3 (improve the construction)
Fourth hat: +2 at every q ≥ 4 (above). SAT: +3/+4 impossible only inside the hat model (q = 5..13), not in general.

## Other records (same paper or a second one)
D = 5 Haar graphs (Haar lemma in Lean; 1152, 1764, 2662 kernel-checked); D = 3 (16,3) 396. Not part of AL's problems.

## Prior art to credit
Delorme 1985 (doubling with levels; all old D = 4 and D = 6 table values), Delorme–Farhi 1984, Bamberg–Law–Penttila 2009
(m-ovoids), Tallini 1988, AL 2020 (and the index slip in their printed matching: i ∈ F* fixes it).
