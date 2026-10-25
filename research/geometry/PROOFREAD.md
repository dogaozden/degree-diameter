# Proofread of geometry.tex (proofread-sonnet, 2026-10-20) — summary

Bottom line: no wrong theorem or proof found.

Findings (being applied to geometry.tex):
1. MEDIUM: abstract/intro claim "iff" for the doubling criterion; only "if" was proved. Necessity is true and short
   (paths between versions with different first letters must pass an element outside A0); added as Thm 3.2(d).
2. MEDIUM: Delorme 1985 citation. Two 1985 papers: "Grands graphes de degré et diamètre donnés", Europ. J. Combin. 6
   (1985) 291–302, and "Large bipartite graphs with given degree and diameter", J. Graph Theory 9 (1985) 325–334
   (DOI 10.1002/jgt.3190090304; abstract: bipartite constructions for every D ≥ 2). Which paper holds the bipartite
   doubling and the D = 4, 6 table constructions is NOT confirmed (no full text). Cite both; co-authors to check.
3–8. LOW: symbol clashes (D, Δ) in Thm 5.6's proof; Table 1 (7,4) regular = 350; Thm 6.3 "exactly 6" clause; cite
   BLP09 for (q+1)/2-ovoids; data pointers for computer examples; Wiki URL http:// + retrieval date; Tallini directly
   for q²−q+1; US spelling.

Citations confirmed: AL20 = Graphs and Combinatorics 38 (2022), no. 4, Art. 110, DOI 10.1007/s00373-022-02500-3;
Payne–Thas section numbers (3.1.1, 3.1.4, 3.1.5, 3.2.1, 3.2.6, 3.3.1, 3.4.1, 3.4.3); Van Maldeghem 2.4.13 (Tits'
equations; draft's equations checked to give a hexagon for q = 3, 5, 7); Thas, JCTA 29 (1980) 87–93 (Hermitian spread);
CDPS22 = J. Combin. Des. 31 (2023) 5–22. All Table 1 "table" values match the Combinatorics Wiki.

Theorem R completion lemma (Lemma 6.10) and Thm 6.11: correct; all counts recomputed (9348, 147500, 386328, 866068,
927724).

Computer re-checks from the draft's own definitions (independent code): four hats p = 5, 7, 11; AL as crossed doubling +
6 patches at q = 5; AS(q) weights q = 3..13; Prop 5.8 q = 3, 5; H(q) lemmas, Thm 6.5 exact whiskers, ν constant,
Lemma 6.6 at q = 3, 5, 7; Thm 6.3 sizes 1020, 1386, 9592; Thm 6.11 pipeline 968, 1224, 9348.

NEW: hand proofs for the two computer-only statements, via a complex structure J_z on Π_z (J_z² = −c, Q(J_z x) = cQ(x),
B(x, J_z x) = 0, and ⟨x, J_z x⟩ is the S_z-line through x): (A) ν = N/D is constant on S-lines since N, D scale by
a² + cb² on ⟨x, Jx⟩; (B) closed form Φ_p(z) = (p2 p3 − p4 p5 + β p2²)/(c p2² + p5²), affine in β, which gives Lemma 6.6.
Checked with sympy. Replaces Remark 6.7 and Appendix A.

# Revision of 2026-10-25 (thm-polish)

Applied with research/theorems/POLISHED.md (which lists the same corrections):
- Table 1: new "2013" column (Miller–Širáň DS14v2, Table 4). It differs from the current table only at (13,3), (15,3):
  270 and 370 in 2013, 274 and 374 after AL20.
- Coordinates and neighbourhoods: full incidence table of the four-hat structure (Table 2, from coords.tex); Remark on
  the normalisation κ1 = 1/2, κ2 = 1/(2ε) of Theorem A and the incidences of the clones; Remark: Corollary C1 written
  inside W(q) (regular spread twice + Singer 2-ovoid), the form proved in Lean; Remark listing the incidences of every
  version in Theorem 6.3; valid (c; c0, c1) for q = 3..13.
- Theorem R: explicit choice of the deleted repeated lines; remark that the completing flags are only proved to exist.
- New Section 9 (Verification): what is Lean-checked, statement by statement, and what is not.
- New Appendix A: the (7,4) example (Q(4,5), 21 shadow lines with stand-ins) in coordinates.
No theorem or value changed. Compiled with TeX Live (latexmk), no undefined references, no overfull boxes.
