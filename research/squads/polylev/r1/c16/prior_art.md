# Card c16 (prior art), squad polylev r1

Director job: thm-polygon-levels, 2026-10-28. Card written 2026-10-28. No construction run, no CPU used.

**Evidence tags.** [read] = I read the text myself (full text extracted from a downloaded PDF with pdftotext, or verbatim).
[read*] = read through the WebFetch tool, which returns a small model's summary, so quotes and numbers are as summarised and
were not checked against the page. [abstract] = abstract or search snippet only. [meta] = bibliographic data only.
[novelty] = carried from `research/lit/novelty-2026-10-25.md` on `origin/claude/novelty-literature-check-4i5frp` (read by me
verbatim; the sources it cites were not re-read by me). [own] = my own derivation, not from a source.

**Wording.** Verdicts are one of "prior art found", "partial overlap", "nothing found in these sources". "Nothing found in these
sources" means only that these searches and reads returned nothing. It is not evidence that the object is unpublished.

## Summary

| Question | Verdict | Closest sources |
|---|---|---|
| 1a. Partition of the points of H(q) into ovoids | nothing found in these sources | Bishnoi and Ihringer, arXiv:1606.07288 [read*]; Thas 1980 JCTA 29 [meta], unread lead |
| 1b. Partition of the lines of H(q) into spreads | nothing found in these sources | arXiv:2312.02397 Prop. 3.15 [read] (a partition of a polar-space line set with H(q) as one class, not of H(q) itself) |
| 1c. Domatic number of the collinearity graph of H(q) | nothing found in these sources | general domatic literature [meta]; GQ fans of ovoids [abstract] |
| 2. Lift of a polygon incidence graph with voltages or colourings to diameter n+3 | **partial overlap** | Delorme 1985 EJC, section 4(c) [read]; bipartite voltage method of Loz, Perez-Roses, Pineda-Villavicencio [read in DS14v2 text, paper not found] |
| 3. Bipartite degree-diameter values at D = 9 or D = 11 published after 2013 | nothing found in these sources | DS14v2 (2013) has D = 9 up to degree 16 and no D = 11 column [read]; the 2026 Comellas table is general graphs [read*] |

**Score: 10 relevant sources read**: nine external sources (DS14v2, Delorme 1985 EJC, Comellas-Gómez arXiv:math/9411218,
arXiv:2312.02397, Comellas arXiv:2406.18994v2, Mendeley dataset v11, Loz-Širáň AJC 2008, arXiv:2005.02427,
arXiv:1606.07288), plus the novelty file. Of these, five were read in full or verbatim and five through WebFetch summaries.

## Part 1: partitions of H(q) into ovoids or spreads, and the domatic number

**Setup [own].** H(q) has N = (q^2+q+1)(q^3+1) points. The collinearity graph has degree q^2+q and each point's 2-ball (the
point and its collinear points) has q^2+q+1 points. An ovoid of H(q) is a set of q^3+1 points pairwise at distance 6 in the
incidence graph (pairwise opposite). A point-set of this kind is "an ovoid of S" in the sense a search snippet gives for
hexagons [abstract]. Two points in one 2-ball are at distance at most 4, so each 2-ball contains at most one ovoid point. Since
(q^3+1)(q^2+q+1) = N, each 2-ball contains exactly one. So an ovoid is a perfect code (efficient dominating set) of the
collinearity graph, and a partition of the points into q^2+q+1 ovoids is a domatic partition into perfect codes. This matches the
HEADER bound k <= q^2+q+1 with equality for a partition into ovoids. Spreads are the dual objects (q^3+1 pairwise opposite lines).

**1a. Partition of points into ovoids: nothing found in these sources.**
- Bishnoi and Ihringer, "Some non-existence results for distance-j ovoids in small generalized polygons", arXiv:1606.07288
  [read*, abstract]. Computer proof that the dual H(4)^D has no distance-2 ovoid, and upper bounds on partial distance-2 ovoids of
  H(q)^D for q = 2 and 4. No partition appears in the abstract. Their introduction, per a search snippet [abstract], says Thas
  studied distance-3 ovoids of hexagons (called simply ovoids) and that distance-j ovoids are tied to perfect codes.
- Distance-2 ovoids of H(q) are known only for q = 2, 3, 4 (De Wispelaere and Van Maldeghem 2008, as cited in Bishnoi and
  Ihringer) [novelty; abstract via search snippet]. This is the notion Bishnoi and Ihringer treat, not the ovoid used in the
  HEADER.
- Thas, "Polar spaces, generalized hexagons and perfect codes", J. Combin. Theory Ser. A 29 (1980) [meta; MaRDI entry
  https://portal.mardi4nfdi.de/wiki/Publication:1144581]. The title ties hexagon ovoids to perfect codes, which is the link in
  [own] above. Not read. It is the first source to read for 1a and 1c.
- H(q) has an ovoid if and only if Q(6,q) has one (Thas, as quoted in a search snippet) [abstract, source not identified].

**1b. Partition of lines into spreads: nothing found in these sources.**
- De Wispelaere and Van Maldeghem, "A distance-2-spread of the generalized hexagon H(3)", Annals of Combinatorics 8 (2004)
  133-154 [meta; MaRDI https://portal.mardi4nfdi.de/wiki/Item:Q1881052 and search snippet]. Their distance-2-spread of H(3) is unique
  with automorphism group L2(13), and H(2) has none [abstract]. This is one spread-type object, not a partition.
- arXiv:2312.02397, "Regular Sets of Lines in Rank 3 Polar Spaces" [read, full text extracted with pdftotext]. Section 3.12: if
  P = O(7,q), P contains the split Cayley hexagon. Proposition 3.15: a line set Y of size (q^(e+2)+1)(q^2+q+1) with the right
  inner distribution can be partitioned into Y1 and Y2 (Lemma 3.14). The (q^2+q+1)-planes form a partial spread. In the equality
  case Y2 is the natural embedding of H(q) in O(7,q). So H(q)'s lines are one class of a partition of Y in a larger polar space. This
  is not a partition of H(q)'s lines into spreads, so the verdict stays "nothing found in these sources". The paper also
  partitions O+(6,q) into copies of O(5,q) (a partial partition g(q), in a later section), which is not about H(q).

**1c. Domatic number of the collinearity graph of H(q): nothing found in these sources.**
- General domatic theory: Haynes, Hedetniemi and Henning survey chapter (2023) [meta, search snippet]; an arXiv 2024 paper on
  domatic partition polynomials, arXiv:2407.00103 [abstract]. Neither concerns generalized polygons.
- Generalized quadrangles, the analogous case: a "fan" of ovoids is a set of s+1 ovoids partitioning the points of a GQ(s,t)
  (Pavese and Zou, near-hexagon paper) [abstract, search snippet]. Brouwer and Wilbrink (1990) determine all ovoids and fans of
  GQ(4,2) [abstract/meta, search snippet]. No hexagon analogue found.
- De Wispelaere and Van Maldeghem, "Regular partitions of (weak) finite generalized polygons", Des. Codes Cryptogr. 47 (2008)
  53-73, DOI 10.1007/s10623-007-9062-9 [abstract, DOI page via search snippet]. "Regular partition" in this paper means a partition
  of a distance-regular graph into regular sets, applied to substructures of generalized polygons. The abstract does not describe
  partitions into ovoids or spreads. Full text not read.

## Part 2: lifts of a polygon incidence graph with voltages or colourings to diameter n+3

**Verdict: partial overlap.** The voltage part overlaps. The colour-class part does not.

**Delorme, "Grands graphes de degre et diametre donnes", Europ. J. Combin. 6 (1985) 291-302,
doi 10.1016/S0195-6698(85)80043-3 [read, full text].** Copy used: https://web.mat.upc.edu/francesc.comellas/delta-d/papers/81981341.pdf
- Section 4 ("Usage des produits"). For the incidence graph G of a generalized quadrangle or hexagon with an orientation (a perfect
  matching oriented point-to-line, others reversed; conditions (i) and (ii)), the products G*Gamma' over groups give:
  (a) G*F4: (Delta+1, D+1, 4n); (b) G*C19: (Delta+2, D+2, 19n); (c) G*C35: (Delta+2, D+3, 35n), with edges over arcs (a,a') given
  by a cyclic voltage; (d) G*S3: (Delta+1, D+2, 6n), where the text says bipartiteness is preserved. The text says (c) works for
  D >= 2 under (i), which for D = 4 or 6 holds for the orientation.
- For the split Cayley hexagon (D = 6, degree q+1, n = 2N), item (c) gives **diameter 9, degree q+3, order 35 x 2N = 70N**. This is a
  diameter n+3 lift of a generalized polygon by a cyclic group voltage, which is the overlap with the question. Bipartiteness of
  (c) is not stated in the text I read. Only (d) is stated bipartite.
- Section 7 (duplication of an induced subgraph A): degree +1 with diameter kept, and bipartiteness kept ("si G est biparti, G' l'est
  aussi"). Read in the EJC text.
- Section 9 (insertion of vertices on edges of a hexagon incidence graph): bipartite, degree q+1, diameter 7, order
  2q(q^4+q^3+3q^2+q+1). Diameter 7, not 9. [read]
- Delorme's general-graph table "valeurs connues (fin 1983)" [read] gives D = 9 values for general graphs. Not bipartite.
- Gap: nothing in this paper uses colour classes or dominating classes of a polygon's point or line sets.

**Comellas and Gómez, arXiv:math/9411218 (1995, Comellas-Gómez compounding paper) [read, intro and section 3].**
Compounding: vertices of the incidence graph H_q of a generalized hexagon are replaced by copies of K_h and the edges are rearranged.
This gives large general graphs of diameter 6 and degree q+1 when q is a prime power. Generalizes Quisquater's single-vertex
replacement in a bipartite Moore graph, and Gómez, Fiol and Serra's several-vertex version. Diameter 6 only, general graphs, no
voltages or colourings. Verdict for D = 6: prior art found for the compounding technique. It does not reach D = 9.

**Compounds in the Comellas table (arXiv:2406.18994v2) [read*].** Table 2 lists operations including "B(T): compound using a
bipartite graph B and a tournament T" and "B(K): substitution of vertices of a bipartite graph", citing Gómez and Fiol 1985. The
table entries themselves are general graphs.

**Not read, but on the list:**
- Gómez and Fiol, "Dense compound graphs", Ars Combin. 20-A (1985) 211-237 [meta]. Cited for the B(T) compound.
- Gómez, Fiol and Serra, "On large (Delta,D)-graphs", Discrete Math. 114 (1993) 219-235 [meta].
- Pineda-Villavicencio, Gómez, Miller, Pérez-Rosés, Networks 53 (2009) 315-328 [abstract, search snippet]. Compounds into a
  bipartite Moore graph of diameter 6, general-graph use.
- Gómez and Miller, Networks (2006) [abstract, search snippet]. General graphs, (15,7), (13,10), (15,10).
- **Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9 (1985) 325-334, doi 10.1002/jgt.3190090304
  [meta/abstract; full text not read].** DS14v2 section 3.4.5 [read] says Delorme's bipartite constructions use "bipartite versions
  of operations described earlier, most notably, *-product and compounding" in [118] and [119] (ref [118] is the EJC paper read above,
  which has bipartite items in sections 7 and 9; ref [119] is this JGT paper). The bipartite version of the section 4 products at
  D = 9 is probably in the JGT paper [own inference]. This is the first paper to check.

**Voltage lifts for bipartite graphs.**
- DS14v2 section 3.4.5 [read]: Loz, Pérez-Rosés and Pineda-Villavicencio "adapted the voltage-assignment-based method developed by
  Loz and Širáň ... to the case of bipartite graphs; this resulted in updating more than one third of the table of the largest known
  bipartite graphs." This is prior art for bipartite voltage lifts in general. The paper itself was not found in any search.
- Loz and Širáň, Australas. J. Combin. 41 (2008) 63-80, https://ajc-new.maths.uq.edu.au/v41.p063 [read*, abstract]. Voltage graphs
  combined with random computer search over (mostly cyclic) semidirect products, for general graphs. No generalized polygon base
  is named in the abstract.
- Base graphs of the bipartite lifts behind the 2013 D = 9 entries are not stated in any source I read, so whether any is a
  polygon lift is unknown.
- Delorme-Gómez-Quisquater "On large bipartite graphs", cited as the source of the D = 7 values in the wiki [novelty]: not found in
  any search. The nearest result is Delorme JGT 1985.

**Colourings (k dominating classes, equal class sizes, 2N(2rk+1) order):** nothing found in these sources.

**Arithmetic check [own].** If Delorme's G*C35 at D = 9 is bipartite, the lab's r = 2 lift of order 2N(4k+1) passes its order 70N at
k = 9 (2N x 37 = 74N; at k = 8 it is 66N). So the threshold is k = 9 at degree q+3, against Delorme's C35 order. The 2013 table
value at the same degree is larger (see Part 3), so C35 is not the table to beat. Caveat: this comparison needs bipartiteness of
(c), which I did not confirm.

## Part 3: bipartite degree-diameter values at D = 9 or D = 11 published after 2013

**Verdict: nothing found in these sources.**

- **DS14v2** (Miller and Širáň, Electron. J. Combin. DS14v2, 2013) [read, full text; https://www.combinatorics.org/files/Surveys/ds14/ds14v2-2013.pdf].
  Table 4 (bipartite, from CombinatoricsWiki "accessed on 10 March 2013") has columns D = 3..10 only. There is no D = 11 column.
  The D = 9 column for Delta = 3..16 is:
  506, 4970, 27936, 117360, 400160, 1091232, 2961536, 7057400, 15200448, 30001152, 50990610, 95087738, 168016334, 288939118.
  Section 3.4.5 [read]: "so far, it is only known that equality holds for D = 2, 3, 4 and 6" (the asymptotic constant for bipartite
  graphs), so no Moore-type value is known at D = 9 or 11.
- **Comellas, "Table of large graphs with given degree and diameter", arXiv:2406.18994v2 (24 Jan 2026)** [read*, WebFetch summary].
  General undirected graphs, diameters 2 to 10, degrees 3 to 16. No bipartite entries. No D = 11 column. The D = 9 general values for
  Delta = 6..16 are 331,387; 1,223,050; 4,243,100; 12,123,288; 27,997,191; 72,933,102; 158,158,875; 249,155,760; 600,123,780;
  1,171,998,164; 2,025,125,476. These are general-graph values and must not be compared with the bipartite column above.
- **Mendeley dataset v11, "Table of Large Degree/Diameter Graphs", 28 Jan 2026** [read*, https://data.mendeley.com/datasets/d75dzbjd4k/11].
  General graphs, "as of January 2026". No bipartite sentence and no D = 9 or D = 11 bipartite values.
- **General-graph Wikipedia table** [abstract, search snippet]: diameters up to 10, no D = 11, not bipartite.
- **Post-2013 bipartite papers that were read or searched**, all at D = 3:
  - Araujo-Pardo and López, arXiv:2005.02427 (Graphs Combin. 38 (2022)) [read*, abstract]. Bipartite family of diameter 3, order
    2(q^2+q+5), records for q = 9 and improvements for q = 11, 13. Diameter 9 and 11 are not mentioned.
  - Araujo-Pardo, Dalfó, Fiol, López, arXiv:2103.11443 (Discrete Math. 344 (2021)) [abstract, search snippet]. Bipartite biregular
    Moore graphs of diameter 3.
  - arXiv:2404.04680 (2024) [abstract, search snippet]. Bipartite biregular graphs of diameter 3.
  - Feria-Purón, Miller, Pineda-Villavicencio, arXiv:1203.3588 (Discrete Math. 313 (2013)) [abstract, search snippet]. Degree 11,
    diameter 3, order 190. Published in 2013, so not after 2013, and D = 3.
- **CombinatoricsWiki bipartite page** (http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs): NOT
  retrieved today. Three WebFetch attempts returned HTTP 503, and curl failed the certificate check against the proxy bundle, so I
  did not disable verification. The novelty file says the page is "as of January 2012" and edited 18 Feb 2022 [novelty]. Whether the
  page now has D = 9 or D = 11 columns is unverified. This is the one source that could change verdict 3, so it should be retried.

**Header thresholds against the 2013 published values [own; the formula is the HEADER's, 2N(2rk+1) with N = (q^6-1)/(q-1)]:**

| q | Delta | r | N | DS14 D=9 value | k that beats DS14 value | HEADER k |
|---|---|---|---|---|---|---|
| 8 | 10 | 1 | 37,449 | 7,057,400 | 47 | 53 |
| 8 | 11 | 2 | 37,449 | 15,200,448 | 51 | 56 |
| 9 | 11 | 1 | 66,430 | 15,200,448 | 57 | 63 |
| 9 | 12 | 2 | 66,430 | 30,001,152 | 57 | 64 |
| 9 | 13 | 3 | 66,430 | 50,990,610 | 64 | 85 |
| 11 | 13 | 1 | 177,156 | 50,990,610 | 72 | 96 |
| 11 | 14 | 2 | 177,156 | 95,087,738 | 67 | 82 |
| 11 | 15 | 3 | 177,156 | 168,016,334 | 79 | 98 |
| 13 | 15 | 1 | 402,234 | 168,016,334 | 104 | 129 |
| 13 | 16 | 2 | 402,234 | 288,939,118 | 90 | 105 |

Reading: every HEADER threshold is above the k that beats the 2013 published value. So the HEADER thresholds must be measured against
the lab's own current values or against a published table I did not find. They are not measured against DS14v2.

## Wording notes for the lab

- Do not say "new" for any of these objects. Use the verdicts above.
- The Comellas 2026 table and the Mendeley dataset are general graphs. Do not put their D = 9 entries next to bipartite orders.
- Delorme 1985 EJC section 4(c) is the closest published overlap for part 2. It is general-graph text, with bipartiteness not stated
  for (c), and it has voltages but no colourings.
- Delorme-Gómez-Quisquater: not found. The wiki citation could not be checked.

## Not read, and what to read next

1. Delorme, J. Graph Theory 9 (1985) 325-334 (doi 10.1002/jgt.3190090304). Check whether the bipartite G*C35 at D = 9 is printed there.
2. Thas, "Polar spaces, generalized hexagons and perfect codes", J. Combin. Theory Ser. A 29 (1980). Check for partitions of H(q)
   into ovoids or spreads, and for a domatic statement.
3. Gómez and Fiol, "Dense compound graphs", Ars Combin. 20-A (1985). Check the bipartite tournament compound B(T).
4. CombinatoricsWiki bipartite page. Retry; check for D = 9 and D = 11 columns and the 2022 edit.
5. Loz, Pérez-Rosés, Pineda-Villavicencio bipartite voltage paper (not found). Check its base graphs.
6. Pérez-Rosés 2012 thesis (Newcastle; server unreachable per [novelty]).

## Sources and where they came from

- Squad header: `research/squads/polylev/r1/HEADER.md` [read].
- Novelty file: `git show origin/claude/novelty-literature-check-4i5frp:research/lit/novelty-2026-10-25.md` [read verbatim].
  `research/lit/` is not present in this checkout.
- Downloaded PDFs (kept in the scratchpad, not in this folder): DS14v2; Delorme 1985 EJC copy; arXiv math/9411218; arXiv 2312.02397.
