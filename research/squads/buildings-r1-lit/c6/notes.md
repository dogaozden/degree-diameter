# c6 notes: pre-2026 asymptotic lower bounds, bipartite degree-diameter problem

Date of search: 2026-10-24 (about 15 minutes). Notation: n_b(Δ,D) = max order of a bipartite graph with max degree ≤ Δ and diameter ≤ D; M_b(Δ,D) = 2((Δ−1)^D − 1)/(Δ−2) (Biggs; survey DS14 p.33). Downloads are in dl/. Page numbers for DS14 come from the journal footers in the PDF.

## Bottom line

- No pre-2026 source I could read states lim n_b/M_b = 1 for any D outside {2,3,4,6}. The best pre-2026 statement, the Miller–Širáň survey (2013), says that for bipartite graphs this is "only known" for D = 2, 3, 4, 6.
- The only pre-2026 bipartite asymptotic for D ≥ 5 I found is Delorme (JGT 1985): for every D ≥ 2, lim inf B·Δ^(1−D) = b_D > 0. The constant is positive but its value is not given in the review, and I did not access the full text.
- lim N·Δ^(−D) = 1 for D = 3 and 5 (Delorme 1985) and for D = 1, 2 is about general graphs, not bipartite. Do not conflate the two problems.

## Per D

### D = 2, 3, 4, 6 (equality cases, for reference)

- Miller & Širáň, "Moore graphs and beyond: A survey of the degree/diameter problem", Electron. J. Combin. DS14, 2nd ed. (2013). URL https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS14 . PDF https://www.combinatorics.org/files/Surveys/ds14/ds14v2-2013.pdf (local copy dl/ds14v2-2013.pdf).
- Page 36 (section 3.4.5), quote: "Delorme also studied the asymptotic behaviour of the problem by introducing the parameter β_D = lim inf_{Δ→∞} b_{Δ,D}/(2Δ^(D−1)). Comparing this with the bipartite Moore bound, we see that β_D ≤ 1 for all D; so far, it is only known [118, 119] that equality holds for D = 2, 3, 4 and 6."
  - The formula is reconstructed from the layout-extracted PDF text; the surrounding sentence fixes the denominator as the bipartite Moore bound scale 2Δ^(D−1).
  - [118] = Delorme, Grands graphes de degré et diamètre donnés, EJC 6 (1985) 291–302. [119] = Delorme, Large bipartite graphs with given degree and diameter, JGT (1985). The survey prints volume 8; the DOI 10.1002/jgt.3190090304 and the 2026 bibliographies give volume 9, issue 3.
- Page 33, quote: "For D = 3, 4, 6 bipartite Moore graphs of degree ∆ have been constructed only when ∆ − 1 is a prime power [41]."

### D = 5 (best: positive constant only; no equality or explicit constant)

- Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9(3) (1985) 325–334, DOI 10.1002/jgt.3190090304, zbMATH Zbl 0623.05048. Read via the zbMATH API review text (LaTeX stripped by me). Quote: "We give constructions of bipartite graphs with maximum degree Δ, diameter D on B vertices, such that for every D ≥ 2 the lim inf_{Δ→∞} B·Δ^(1−D) = b_D > 0. We also improve similar results on ordinary graphs, for example, we prove that lim_{Δ→∞} N·Δ^(−D) = 1 if D is 3 or 5. This is a partial answer to a problem of Bollobás."
  - Status: review only. The Wiley page returned HTTP 403 and the full text was not read. The value of b_5 is not stated in the review.
  - Consistency check: the survey (p.36) says equality in β_D is known only for D = 2, 3, 4, 6, so b_5 < 1 is what is known for bipartite D = 5.
- General-graph statement, NOT bipartite. Survey p.19, quote: "Delorme [119] introduced the parameter µ_D = lim inf_{∆→∞} n_{∆,D}/∆^D. Trivially, µ_D ≤ 1 for all D, and µ_1 = 1; the bound (6) shows that µ_2 = 1 as well. Further results of Delorme [118] imply that µ_D is equal to 1 also for D = 3 and D = 5." The n here is for general graphs.
- Largest known bipartite orders, survey Table 4 (p.37, non-asymptotic, 2013). The D=5 column is b_{3,5} = 56 (Bond–Delorme, optimal by Jørgensen, survey p.36, b_{3,5} = B_{3,5} − 6), with b_{4,5} = 160, b_{5,5} = 336, b_{6,5} = 684. The ratios to M_b (my computation from the table and the Biggs formula) are 0.903, 0.661, 0.493, 0.438 for Δ = 3, 4, 5, 6.
- Constraint, survey p.34 (Feria-Purón, Miller, Pineda-Villavicencio), quote: "and the non-existence of bipartite graphs of degree ∆ ⩾ 3, diameter D ⩾ 5 and defect 4." This rules out defect 4 for D = 5, but it is not an asymptotic statement.

### D = 7, 8, 9, 10

- No pre-2026 explicit asymptotic constant for bipartite D ≥ 7 found. Only the qualitative Delorme statement above (b_D > 0 for every D ≥ 2) and the 2013 table.
- Table 4 values (non-asymptotic, fixed Δ), with ratios to M_b computed by me. Δ = 3: D7 168 (0.661), D8 256 (0.502), D9 506 (0.495), D10 800 (0.391). Δ = 4: D7 840 (0.384), D8 2184 (0.333), D9 4970 (0.253), D10 11748 (0.199).

## General-graph context (not bipartite; for awareness)

- Canale & Gómez, "Asymptotically large (Δ,D)-graphs", Discrete Appl. Math. 152 (2005) 89–108, DOI 10.1016/j.dam.2005.03.008, Zbl 1080.05027. zbMATH keywords: degree-diameter problem, de Bruijn digraph, Kautz digraph, exchange graph, graph-digraph product. Survey p.18, quote: "A substantial progress was achieved by Canale and Gómez [84] by exhibiting, for an infinite set of values of ∆, families of graphs showing that ... for all D ⩾ 3; the constant in the denominator can be replaced by 1.57 for D congruent with −1, 0, or 1 (mod 6)." The abstract was not retrieved (Elsevier redirect stub). No bipartite content found (unverified).
- Cames van Batenburg & Korsky (arXiv:2608.03965, 2026) and Isham et al. (arXiv:2608.27253, 2026) are already known and not counted. Their bibliographies were used only as leads. CvB–Korsky's intro says the general-graph conjecture "was previously known only for k ∈ {2, 3, 5}, through constructions arising from finite generalized polygons [16, 17, 3]". Their bipartite remark ("this also shows that the limit is 1 when restricted to bipartite graphs") concerns the edge / line-graph version h_ℓ(d), not n_b.
- Comellas & Gómez, "New large graphs with given degree and diameter", arXiv math/9411218 (1994), https://arxiv.org/abs/math/9411218 (PDF in dl/). Their bipartite statement, PDF p.3, quote: "The bipartite graphs that attain the bound are called bipartite Moore graphs. They exist only for D = 2 (complete bipartite graphs K∆,∆) or D = 3, 4, 6." No asymptotic bipartite statement found in the parts I read.

## zbMATH and other checks

- Bond & Delorme, "New large bipartite graphs with given degree and diameter", Ars Combin. 25C (1988) 123–132, Zbl 0649.05043. Review quote: "The double cover construction of N. Biggs ... is used to produce large bipartite graphs of given maximal degree Δ and diameter D. E.g. for Δ = 3 and D = 5 a graph with 56 vertices is given. A table is presented of best known orders if 3 ≤ Δ ≤ 16 and 3 ≤ D ≤ 10 with the corresponding references." Non-asymptotic.
- Not read: Delorme, "Examples of products giving large graphs with given degree and diameter", DAM 37/38 (1992) 157–167, Zbl 0768.05034 (metadata only). Delorme & Gómez, "Some new large compound graphs", EJC 23 (2002) 539–547, Zbl 1017.05089 (metadata only).
- Not used: Dalfó, Huemer & Salas (2016) on maximal planar bipartite graphs (planar subclass; snippet only, unverified).

## Caveats

- The survey's "J. Graph Theory 8" volume for Delorme [119] conflicts with the DOI and the 2026 bibliographies (volume 9). I use volume 9.
- The b_D constants are asserted to exist but are not given numerically in anything I could read.
- The Canale–Gómez abstract is unverified; I could not confirm whether it has any bipartite section.

## Leads for next round

1. Full text of Delorme JGT 9 (1985) 325–334 (Wiley 403; try a library copy or MathSciNet): is b_5 given explicitly, and how is it constructed (generalized quadrangles or hexagons, or compounding)?
2. Delorme DAM 1992 (Zbl 0768.05034) and Delorme & Gómez EJC 2002 (Zbl 1017.05089): check for bipartite products with explicit asymptotic constants.
3. Feria-Purón & Pineda-Villavicencio, arXiv:1010.5651 (defect ≤ 4 catalogue, nonexistence for D ≥ 5). Context only.
