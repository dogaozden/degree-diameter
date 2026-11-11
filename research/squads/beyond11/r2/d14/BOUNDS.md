# d14: proven upper bounds for D = 11, 12 (Δ = 11..14 at D = 11; Δ = 11..13 at D = 12)

Source: R. Feria-Purón, G. Pineda-Villavicencio, "On bipartite graphs of defect at most 4", arXiv:1010.5651 (v2, 7 Jun 2011),
published as Discrete Applied Math. 160 (2012) 140-154, doi 10.1016/j.dam.2011.09.002. Fetched 2026-11-01 (arxiv.org/abs and
arxiv.org/pdf/1010.5651, 26 PDF pages). Local copy: d14/paper.pdf, text in d14/paper.txt. Page numbers below are PDF page numbers
of the arXiv version (not the journal page numbers). I did not check the journal typeset version.

Notation: Mb(Δ,D) = 2 S, S = 1 + (Δ-1) + ... + (Δ-1)^(D-1) (the Moore bipartite bound; inferred from the order 2S-4 used in
Prop. 5.1, p.15-16). A bipartite (Δ,D,-ε)-graph has defect ε.

## Quoted statements

1. Prop. 6.4 (p.25), the bound the table uses:
   "For natural numbers Δ >= 3 and 5 <= D <= 187 (D != 6), Nb(Δ,D) <= Mb(Δ,D) - 6."
   It is listed in the paper as a consequence of the catalogues (Conclusions, p.23-24), not proved on its own.

2. Defect 4, odd D (Theorem 5.2, p.19): "There are no bipartite (d,D,-4)-graphs for d >= 3 and odd D >= 5."
   Proof sketch on p.19: N = (2S-4)/(D-1) short cycles, Repeat Cycle Lemma pairs them up, so N must be even, but N is odd for odd D.

3. Defect 4, D-1 an odd prime power (Corollary 5.1, p.17): "There is no bipartite (d,D,-4)-graph with d >= 3 and D >= 5 such
   that D - 1 is an odd prime power." Proof is the mod-p computation on p.16-17 using Prop. 5.1 (p.15-16).
   D = 12 has D-1 = 11, an odd prime, so this applies to every Δ >= 3 at D = 12.

4. Defect 4, all 5 <= D <= 187 (Theorem 5.3, p.20): "The path of length 5 is the only bipartite (Δ,D,-4)-graph with Δ >= 2
   and 5 <= D <= 187." The text says this follows from Theorem 5.2 and Prop. 5.1. For even D >= 6 and Δ >= 4 no argument beyond
   the integrality count is written out. I did not rely on Theorem 5.3 for the cells below.

5. Defect 2 (p.4, Sec. 3): "Such graphs do not exist when Δ >= 3 and D >= 4; see [5, 6, 14]."

6. Regularity (Props. 3.1, 3.2, p.4): for ε < 1 + (Δ-1) + ... + (Δ-1)^(D-2), Δ >= 3, D >= 3, every bipartite (Δ,D,-ε)-graph is
   regular. Defects 1, 3 (and 5, at D >= 5) are therefore impossible. p.25 says the same for ε = 5 and states that a regular
   such graph "cannot exist". The fact used is that a regular bipartite graph of diameter D has at least Mb vertices. The paper
   uses this without proof, and I did not check it. It is the standard regular Moore bipartite bound.

7. Moore graphs (p.4): "For other values of D >= 2 and Δ >= 3 there are no Moore bipartite graphs (see [15, 9])." Here [9] is
   Feit-Higman 1964, [15] is Singleton 1966. D = 11 and 12 are not in {2, 3, 4, 6}, so Nb < Mb.

## Bounds

Cell (Δ,11), Δ = 11, 12, 13, 14: Nb(Δ,11) <= Mb(Δ,11) - 6. Proven, and the paper states it as Prop. 6.4 (p.25).
   Independent route (no reliance on Thm 5.3): defect 0 excluded by item 7; defects 1, 3, 5 excluded by item 6; defect 2 by
   item 5; defect 4 by Theorem 5.2 (item 2, D = 11 is odd). So defects 0..5 are all excluded.

Cell (Δ,12), Δ = 11, 12, 13: Nb(Δ,12) <= Mb(Δ,12) - 6. Proven, Prop. 6.4 (p.25); D = 12 is not 6 and lies in 5..187.
   Independent route: defect 0 by item 7; defects 1, 3, 5 by item 6; defect 2 by item 5; defect 4 by Corollary 5.1 (item 3),
   since 12 - 1 = 11 is an odd prime. Corollary 5.1 holds for all Δ >= 3, so it covers all three cells.
   Cross-check: d14/check.py reproduces the Prop. 5.1 integrality test. For D = 12, (D-1) = 11 divides 2S-4 for no residue of
   d-1 mod 11, so no defect-4 graph exists for any d >= 3. For D = 11, the residues d-1 = 2, 7 mod 10 pass the test, which is why
   D = 11 needs Theorem 5.2 (odd D) and not the integrality count.

Correction to round-1 claim (card c14): defect 4 is NOT excluded only for odd D. Corollary 5.1 (p.17) and Theorem 5.3 (p.20) also
exclude it at D = 12, so D = 12 has M_b - 6, not M_b - 4. The paper's own Conjecture 6.1 (p.25) still says "no (Δ,D,-4) for
Δ >= 3 and D >= 5", which is strange if Theorem 5.3 covers 5 <= D <= 187. The paper does not reconcile these. That tension does
not affect the two cells above, because Corollary 5.1 and Theorem 5.2 settle them directly.

## Caveats
- Journal version (2012) not checked. Numbering and theorem statements may differ from arXiv v2.
- Items 5-7 are quoted from the paper, which cites [5, 6, 14] and [9, 15]. I did not check those references.
- Mb(Δ,D) = 2S is inferred from the paper's order formula, not quoted from it.
- No search was run. The bounds are paper results, not computed here. Nothing was checked by search code.
