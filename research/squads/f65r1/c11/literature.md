# c11 literature card (round f65r1): bipartite (6,5) records, bounds, techniques

Time box about 25 min. Read-only web use. Downloaded PDFs are in `c11/dl/` (text extracted with pdftotext; the
arXiv PDFs were fetched directly, so quotes below are from the PDF text, not from a summary).

Legend: **PDF** = quote checked in the downloaded PDF text. **WEB** = quote from a web page or search snippet, not
checked in full. **INFERRED** = my reasoning.

## Q1. How was the 684 graph built?

- Nothing new beyond what the lab already has in `research/lifts/LITERATURE.md` (same sources). I could not open
  Loz's thesis (ResearchSpace handle 2292/52008, full text restricted) or his data page (eyal.com.au, parked).
- The 2026 Comellas survey (below) credits the orange cells to Loz with the label "Graphs built by E. Loz [27]"
  (arXiv 2406.18994v2, legend of Table 2). It gives no voltage data.
- Feria-Purón, Miller, Pineda-Villavicencio 2013 is the only published bipartite voltage lift found (their (7,3)=80,
  Z5 ⋊ Z8 dipole). Already in LITERATURE.md §4.
- INFERRED: the orange bipartite cells are most likely loopless quotients over metacyclic groups (Loz–Pérez-Rosés–
  Pineda-Villavicencio). No voltage assignment for (6,5) is public.

## Q2. Any larger bipartite (6,5) since 2013? Any new D = 5 bipartite values for Δ = 4..12?

**No.** I found no bipartite (6,5) graph above 684 and no new bipartite D = 5 value.

- **CombinatoricsWiki bipartite table** (http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs):
  the lab's notes say the last value change was 30 Mar 2021 for (13,3) and (15,3), and nothing in our cells changed
  after Jan 2012. Not re-checked this session (the wiki was not reachable over https from this container, as noted
  in LITERATURE.md). WEB only.
- **Hafner's bipartite page** (https://www.math.auckland.ac.nz/~hafner/bipartite/), header "Some large bipartite
  graphs." (WEB, fetched and summarised): the only (6,5) file is "6.5 | 6 | 5 | 660 | None given". Other D = 5 files:
  4.5 (160), 7.5 (1000), 8.5 (1596). All below the table values, which is consistent with the lab note.
- **Comellas, "Table of large graphs with given degree and diameter", arXiv:2406.18994v2 (24 Jan 2026)** (PDF). Table 1
  is "Largest (∆, D)-graphs (January 2026)". It is a GENERAL table; its keywords are "Large Graphs, Degree-Diameter
  Problem, Cayley Graphs". The PDF text has no bipartite table and no bipartite marks. Its Δ = 6 row reads
  "6 32 111 390 1 404 7 917 19 383 76 891 331 387 1 253 615", so the general (6,5) entry is 1404. That is a general
  graph, not a bipartite record. The 2024 general (3,5)=70 etc. confirm the same column layout.
- **Comellas's UPC pages** (desc_g*.html): general tables only; the diameter-6 page was last modified 15 Oct 2026
  (WEB). No bipartite table.
- **arXiv:2606.15860** (14 Jun 2026, "New lower bounds for the degree/diameter problem via interaction with a
  browser-accessible LLM") (WEB): diameter-5 values only for Δ = 12 (34,992) and Δ = 16 (147,456). It does not
  mention bipartite graphs. Method: a Z4×Z6 voltage lift of a 6-vertex multigraph, then lifts over GF(3)^5 and GF(4)^5
  with affine route charts. This is the route-chart lift the lab already tried (≤ 384).
- **arXiv:2608.27253** (Isham, Lakhotia, Monroe, Petrini, "Kronecker Products, Polarity Quotients and Large Graph
  Constructions", submitted 27 Aug 2026, v2 22 Oct 2026) (WEB, abstract): gives Kronecker-product families "for
  diameters 2, 3, and 5 from generalized polygons", and a diameter-3 degree-18 record. It has no Δ = 6, D = 5 value
  (WEB summary; the full text was not extractable from the PDF here).
- Search for a 2020–2026 bi-Cayley / bipartite Cayley record table: none found. Abas–Vetrík (below) is the newest
  bipartite-Cayley bound found, and it is from 2016.

## Q3. Upper bounds for bipartite (6,5)

- Moore bipartite bound (INFERRED from the formula, which is PDF-checked in Comellas–Gómez 1994, arXiv math/9411218, §1):
  "b(∆, D) ≤ 2((∆−1)^D − 1)/(∆−2)". For Δ = 6, D = 5: 2·3124/4 = **1562**.
- **Feria-Purón & Pineda-Villavicencio, "On bipartite graphs of defect at most 4", arXiv:1010.5651v2** (published
  Discrete Appl. Math. 160 (2012) per LITERATURE.md's bibliography; PDF text checked):
  - Abstract (PDF): "a non-existence proof of all bipartite (∆, D, −4)-graphs with ∆ ≥ 3 and odd D ≥ 5". So for
    (6,5), order 1558 is impossible. (Note: a WEB summary of the abstract said "odd D ≥ 7". The PDF says D ≥ 5. D = 5
    is handled by Prop. 5.1 in §5.)
  - Abstract (PDF): "we conjecture that there are no bipartite graphs of defect 4 for ∆ ≥ 3 and D ≥ 5".
  - §6.2 (PDF): "a bipartite (∆, D, −5)-graph Γ with ∆ ≥ 3 and D ≥ 5 must be regular (by Proposition 3.1) and thus
    cannot exist." So defects 4 and 5 are both excluded for (6,5).
  - **Proposition 6.4 (PDF): "For natural numbers ∆ ≥ 3 and 5 ≤ D ≤ 187 (D ≠ 6), Nb(∆, D) ≤ Mb(∆, D) − 6."**
    So **Nb(6,5) ≤ 1562 − 6 = 1556**. Proposition 6.3 gives the same for D ≡ 5 (mod 6), and D = 5 is covered.
  - Conjecture 6.2 (PDF): "Nb(∆, D) ≤ Mb(∆, D) − 6" for all ∆ ≥ 3, D ≥ 5, D ≠ 6.
  - Practical reading: the true gap is huge (684 vs 1556). These defect results say nothing about whether 686 exists,
    but they do show the search space is not truncated by the Moore-type bound.
- arXiv:2509.01825 (Sept 2025, bipartite graphs with given diameter and connectivity; edge-count problem) is not about
  vertex order at Δ = 6 and has been called unreliable by a review. Not used.

## Q4. Techniques for bipartite diameter 5 (or odd diameter) NOT Haar, cyclic/metacyclic lift, or generalized polygon

Candidates, each checked against the exclusion list:

1. **Substitution / compound of a bipartite graph** (Comellas–Gómez 1994, arXiv math/9411218; Gómez–Pelayo–Balbuena
   1999 *Networks* 34:154–161): "The graphs are constructed from Moore bipartite graphs by replacement of some vertices
   by adequate structures" (PDF, abstract). The replacement in the paper is by complete graphs K_h, so the result is
   NOT bipartite. A bipartite version would substitute by an edgeless or K_{h,h} structure and would need its own
   distance analysis. It is also built on a Moore bipartite base, which does not exist at D = 5. Probably the best
   "new" family, but unexplored for bipartite targets.
2. **Vertex duplication** (Gd, Gd+; Comellas 2026 legend "Gd duplication of some vertices of G"): general graphs.
   Not checked for bipartiteness.
3. **Polarity quotient of a bipartite graph** (B′; Delorme; Comellas 2026 legend "quotient of the bipartite graph B by a
   polarity"): it gives non-bipartite general graphs. Polarity quotients of generalized polygon incidence graphs
   are excluded by rule 4.
4. **Kronecker product of bipartite graphs with polarity, then polarity quotient** (arXiv:2608.27253; Abas's ⊗B′ in
   the 2026 table): its D = 5 families use generalized polygons, so they are excluded.
5. **Bipartite Cayley digraphs of odd diameter k ≥ 5** (Abas–Vetrík, arXiv:1603.06013, PDF text). Abstract: "bipartite
   Cayley digraphs of order 2(k − 1)⌊d/2⌋^(k−1) and diameter at most k, where k ≥ 5" (odd k). For d = 6, k = 5 this
   gives 2·4·3^4 = **648** (INFERRED arithmetic). It is a digraph bound, and 648 < 684, so it is not a lead on its own.
   A group of order ~690 with an undirected analogue would be a different question.
6. **Conder's (5,5)=648 Cayley graph** (Comellas 2026, §2.4, PDF): a Cayley graph on group 279 of order 648, not
   bipartite. Not a lead for (6,5).

## Summary of numbers (all dated)

| quantity | value | source |
|---|---|---|
| bipartite Moore bound Mb(6,5) | 1562 | formula, Comellas–Gómez 1994 |
| best known bipartite (6,5) | 684 | 2013 table (lab notes), no later bipartite value found |
| Hafner bipartite file 6.5 | 660 | hafner page, unattributed |
| general (6,5) record | 1404 | Comellas 2026 table, Jan 2026 (general, not bipartite) |
| general (6,5) in 1994 | 1200 | Comellas–Gómez 1994 Table 1 |
| upper bound Nb(6,5) | ≤ 1556 | Feria-Purón & Pineda-Villavicencio Prop. 6.4 (PDF) |
| defect 4 for bipartite (Δ≥3, odd D≥5) | impossible | same paper, abstract (PDF) |

## Next (for the director)

The one untried, non-excluded family is a bipartite-preserving vertex substitution (Comellas–Gómez style) applied to a
bipartite base of order ~650–690 with a diameter-5-friendly structure. The literature only gives the K_h version,
which breaks bipartiteness, so this would be a new construction, not a copied one.
