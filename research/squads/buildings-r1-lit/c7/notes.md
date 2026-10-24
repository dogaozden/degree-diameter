# c7 notes: generalized polygons in degree-diameter and cage literature

Scope: directions (a)-(d) of card c7. Sources were fetched and converted with pdftotext into `c7/dl/` (texts `*.txt` next to the PDFs). Quotes were checked against that extraction; where the extraction garbles symbols, the quote is marked OCR. Anything not opened is marked unverified.

## Bottom line

- No pre-2026 source found that states an asymptotic Moore result for D = 7 (general) or D = 8 (bipartite). The closest pre-2026 statements are negative: Bachratý (2021) says no octagon-based degree-diameter construction is known.
- Delorme-type products are in a pre-2026 table with explicit parameters, but only for quadrangles (D = 3, including the biregular GQ(2,4) factor at Delta = 15) and the hexagon H(3) (D = 5). No octagon entry.
- The table's orders equal |points| x |lines| of the factor (checked arithmetic below). This matches the octagon construction described in the task, with D = n - 1 for the quotient and D = n for the bipartite component.
- (d): no degree-diameter paper using partial flags, polar spaces or other higher-rank building incidence graphs was found.

## (a) Benson 1966 (what it constructs)

- Reference: C. T. Benson, "Minimal regular graphs of girths eight and twelve", Canad. J. Math. 18 (1966), 1091-1094. DOI 10.4153/CJM-1966-109-8. zbMATH 0146.45701 (https://zbmath.org/3236773, record fetched via API). Full text: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/EC5B825B2578C1FA6A6D5F61E52EBC0B/S0008414X00041055a.pdf/minimal-regular-graphs-of-girths-eight-and-twelve.pdf (saved as `dl/benson1966.pdf`).
- Quote (p. 1091): "Here we construct these graphs making only incidental use of group theory."
- Quote (p. 1091, Lemma 1): "No set of points and lines in Q4 form a triangle."
- Theorem 1 (p. 1091, OCR): nodes are the points and lines of a non-degenerate quadric in P(4,q), joined when incident. OCR: "Then G g is a minimal regular graph of degree q + 1 and girth 8." This is the incidence graph of the generalized quadrangle Q(4,q) of order (q,q). Benson's count (p. 1092, OCR): "1 + q + q2 + qz points and 1 + q + q2 + qz lines in QA", i.e. (q+1)(q^2+1) each.
- Theorem 2 (p. 1091, OCR): nodes are the points of a quadric in P(6,q) and a distinguished family of lines, giving a minimal regular graph of degree q + 1 and girth 12. The identification with the split Cayley hexagon H(q) is mine (the paper does not name it). Lemma 2 counts (q+1)(1+q^2+q^4) points (OCR), i.e. the points of H(q).
- Relevance: the regular case s = t (Tutte bound attained). No degree-diameter content. The Comellas table (below) cites Benson as the source of its building blocks: "Hq Incidence graph of a regular generalized hexagon [3]" and "Qq Incidence graph of a regular generalized quadrangle [3]", with ref [3] = C. T. Benson (arXiv:2406.18994, Table 2 and references).

## (b) Octagons in degree-diameter work

1. Bachratý, M., "Generalised polygons in the degree-diameter problem", summary of PhD dissertation, Slovak University of Technology Bratislava, submitted 31 May 2021. URL: https://www.svf.stuba.sk/buxus/docs/autoreferaty/2020-21/bachraty.pdf (`dl/bachraty.pdf`). Section 5.2 "Degree-diameter problem and generalised octagons", pp. 22-23.
   - Quote: "In contrast, there is not a single known construction (relevant to this problem) based on generalised octagons."
   - Quote: "Nevertheless, we believe that Ree-Tits octagons are worth of investigation in the context of the degree-diameter problem."
   - Quote: "There is no obvious way to turn this graph into a graph of diameter 7" (the graph is the Ree-Tits incidence graph L(q); the text adds "Moreover, by Lemma 2.1.4 we know that L(q) has diameter 8.")
   - Suggested next family: orthogonal quadrangles Q(5,q), which are the (s,t) = (q,q^2) family with a simpler structure.
   - This is the strongest pre-2026 negative for D = 7 via octagons. It does not discuss the side-swapped Kronecker (Delorme) product for D = 8 bipartite.
   - The same summary (abstract, Slovak; my translation): "It is known that this is possible for diameters 2, 3 and 5." The original: "Je známe, že to je možné pre priemery 2, 3 a 5."

2. Bachratý, Šiagiová, Širáň, "Asymptotically approaching the Moore bound for diameter three by Cayley graphs", arXiv:1709.09760 (27 Sep 2017). URL: https://arxiv.org/abs/1709.09760 (`dl/arxiv_1709.09760.pdf`). Page 2:
   - Quote: "The best available result addressing Delorme's problem is his own observation [6] that lim sup n(d,k)/M(d,k) = 1 for k in {2, 3, 5}." (subscript d -> infinity lost in extraction)
   - Quote: "This follows by taking polarity quotients of the incidence graphs of generalised n-gons admitting a polarity (cf. [17]) for n in {3, 4, 6}, respectively."
   - Quote: "For the remaining diameters the best currently known results on Delorme's problem are much weaker but far from easy to prove."
   - Quote: "and from [4] we have lim sup n(d,k)/M(d,k) >= (1.6)^{-k} for k >= 6, where 1.6 can be replaced by 1.57 for k = -1, 0, 1 mod 6." Here [4] = E. A. Canale and J. Gómez, "Superfluous edges and exponential expansions of de Bruijn and Kautz digraphs", Discrete Appl. Math. 138 (2004), 303-331 (as cited; not opened, so unverified).
   - Arithmetic (mine): for k = 7 the general bound is about 1.57^{-7} = 0.042 of Delta^7 (or 1.6^{-7} = 0.037), far from 1.

3. Erskine, G., Tuite, J., "Large Cayley graphs of small diameter", arXiv:1708.02425 (v2, 12 Apr 2018), URL https://arxiv.org/abs/1708.02425 (`dl/arxiv_1708.02425.pdf`). Cayley graphs only. Journal venue (Discrete Appl. Math., 2018) taken from a search summary, unverified.
   - Quote (abstract): "Our diameter 3 construction is, as far as we know, the first to employ matrix groups over finite fields in the degree-diameter problem."
   - Theorem 4.1 (Sec. 4, pp. 14-15): "For odd k >= 7," with bound L^-(k) >= (2/3)^k read from the extracted fraction "2k / 3k" (reading, unverified against the typeset page). For k = 7 this is about 0.0585 of Delta^7 (my arithmetic).

4. Comellas, F., "Table of large graphs with given degree and diameter", arXiv:2406.18994. URL: https://arxiv.org/abs/2406.18994. Two versions: v1 (27 Jun 2024, caption "Table 1: Largest (Delta, D)-graphs (June 2024)"); v2 (24 Jan 2026, caption "(January 2026)"). Saved as `dl/arxiv_2406.18994.pdf` and `dl/arxiv_2406.18994v1.pdf`.
   - No octagon symbol appears in the notation table (Table 2) or in Table 1. No octagon-derived entry.
   - Notation, v1 (ref [13] = C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9 (1985) 325-334, as printed by Comellas; arXiv:1709.09760 prints vol. 8): "⊗B The component with polarity of the cartesian product of a bipartite graph B by itself [13]." (v2 cites it as [15].) My reading: "cartesian" is the side-swapped tensor product component A x B union B x A.
   - Entries with explicit parameters (Delta, D, order), present in v1 (June 2024) and v2:
     - (15, 3): 1215, "(⊗Q_{2,4})'". Q(2,4) is a generalized quadrangle of order (2,4), biregular with degrees 3 and 5, so Delta = 3 x 5 = 15. Quotient order 27 x 45 = 1215 (|points| x |lines|).
     - (16, 3): 1600, "(⊗Q_3)'". Q(3,3): 40 x 40 = 1600.
     - (16, 5): 132496, "(⊗H_3)'". H(3): 364 x 364 = 132496.
   - So the table's orders equal |points| x |lines| of the factor, i.e. the polarity quotient of the side-swapped component of size 2|P||L|. The quotient has diameter n - 1 (3 for n = 4, 5 for n = 6) (table pattern; my check of the n = 8 analogue below).
   - Table D = 7 column (my arithmetic, ratio to Delta^7): Delta = 10: 583083 (0.058); 15: 8599986 (0.050, entry "Loz"); 16: 14882658 (0.055, entry "K1 Sigma8 H13"). No D = 7 entry is octagon-derived.

5. Araujo-Pardo, Dalfó, Fiol, López, "Bipartite biregular Moore graphs", arXiv:2103.11443 (21 Mar 2021). URL: https://arxiv.org/abs/2103.11443 (`dl/arxiv_2103.11443.pdf`).
   - Abstract quote: "This problem was introduced in 1983 by Yebra, Fiol, and Fàbrega." (the bipartite biregular diameter problem)
   - Theorem 3.1 (p. 10, citing [1] = Araujo-Pardo, Jajcay, Ramos Rivera, submitted 2020): "Whenever a generalized quadrangle, hexagon, or octagon G of order (s, t) exists, its point-line incidence graph is an (s + 1, t + 1; 8)-, (s + 1, t + 1; 12)- or (s + 1, t + 1; 16)-cage, respectively."
   - p. 11: "for n = 8, we have the generalized octagons, which are only known to exist for the pairs (q, q^2), (q^2, q), where q is an odd power of 2."
   - Theorem 3.4 (p. 11, citing van Maldeghem Cor. 1.5.5): for n = 8, "|P| = (1 + r)(1 + rs)(1 + r^2 s^2) and |L| = (1 + s)(1 + rs)(1 + r^2 s^2)." At (r,s) = (2,4) this gives 1755 and 2925, matching the known GO(2,4) counts.
   - No degree-diameter content for octagons; it studies D = 3, 4, 5, 6.

6. Araujo-Pardo, Ramos-Rivera, Jajcay, "Bipartite biregular cages and block designs", arXiv:1907.11568 (26 Jul 2019). URL: https://arxiv.org/abs/1907.11568 (`dl/arxiv_1907.11568.pdf`).
   - Abstract (line-broken in extraction): "Considering girths higher than 6 and prime powers s, we relate the existence of generalized polygons (quadrangles, hexagons and octagons) with the existence of (n + 1, n^2 + 1; 8), (n + 1, n^3 + 1; 12), and (n + 1, n^2 + 1; 16)-bipartite biregular Moore cages, respectively."
   - Abstract: "In their 2019 paper, Filipovski, Ramos-Rivera and Jajcay present lower bounds on the orders of bipartite biregular (n, m; g)-graphs, and call the graphs that attain these bounds bipartite biregular Moore cages."
   - Sec. 2: "for r = 8, we have the generalized octagons, which only exist when s = t^2."

7. Araujo-Pardo, Kiss, Szőnyi, "A little more about bipartite biregular cages, block designs and generalized polygons", arXiv:2310.12137 (18 Oct 2023). URL: https://arxiv.org/abs/2310.12137 (`dl/arxiv_2310.12137.pdf`).
   - Abstract quote: "For girth g = 2r and r = {4, 6, 8}, we use results on t-good structures given by ovoids, spreads and sub-polygons in generalized polygons to obtain (m, n; 2r)-bipartite biregular graphs."
   - So pre-2026 work covers octagon-based (girth 16) bipartite biregular graphs. Not degree-diameter.

8. Filipovski, Ramos-Rivera, Jajcay, "On biregular bipartite graphs of small excess", Discrete Math. 342 (2019) 2066-2076 (reference [8] of 2103.11443). Not opened; unverified.

## (c) Biregular Moore bounds and higher-rank buildings

- The biregular Moore/cage line (items 5-7 above) is pre-2026 and treats octagons explicitly (girth 16, (s+1, t+1; 16)-cages).
- None of the downloaded texts mentions flags of higher-rank buildings. A case-insensitive grep over all texts for flag, building, Tits, Ree and octagon found only generalized-polygon-level material and the Ree-group remarks in Bachratý.
- Araujo, López, "On new record graphs close to bipartite Moore graphs", arXiv:2005.02427 (5 May 2020; `dl/arxiv_2005.02427.pdf`) has no mention of polygons. Its open Problem 4 asks for bipartite regular graphs of diameters 4 and 6 (no construction).

## (d) Partial flags, polar spaces and higher-rank incidence graphs

- Not found. Web searches on partial flags, polar spaces, metasymplectic spaces and flag/building incidence graphs in the degree-diameter setting returned nothing relevant before 2026.
- Related, weaker (score 1 level):
  - Kiss, Kovács, Kutnar, Ruff, Šparl, "A note on a geometric construction of large Cayley graphs of given degree and diameter", Studia Univ. Babeš-Bolyai Math. 54 (2009). URL: https://www.cs.ubbcluj.ro/journal/studia-mathematica/archive/2009-3/kiss.pdf (`dl/kiss2009.pdf`). Quote (abstract): "The graphs arise from arcs, caps and other objects of finite projective spaces." (projective spaces, not flags).
  - Delorme 1992, "Examples of products giving large graphs with given degree and diameter", Discrete Appl. Math. 37/38 (1992) 157-167. Cited in arXiv:1709.09760 for lim sup n(d,4)/M(d,4) >= 1/4. Not opened; unverified.
  - Canale and Gómez 2004 (Kautz/de Bruijn expansions): see item (b)2.

## Checked arithmetic (mine, not in any source; diameter claims unverified)

- GO(2,4) (r = 2, s = 4 in the 2103.11443 convention): |P| = 3 x 9 x 65 = 1755, |L| = 5 x 9 x 65 = 2925, Delta = (r+1)(s+1) = 15.
- Side-swapped component A x B union B x A: 2 x 1755 x 2925 = 10266750 vertices. Bipartite, degree 15. My distance argument: same-part distances are at most 8 and cross-part distances at most 7, so the bipartite component has diameter 8 and the quotient by the side swap has diameter at most 7.
- Quotient order |P||L| = 5133375, i.e. 0.030 of Delta^7. The table record at (15,7) is 8599986, so at q = 2 the octagon quotient (if it had diameter 7) would not beat the table. The ratio (1+q^3)^2(1+q^6)^2 / ((1+q)^6(1+q^2)^6) tends to 1 (my algebra), so the construction matters only asymptotically.
- Bipartite Moore bound M_b(15,8) = 2 sum_{i=0}^{7} 14^i = 227044470 (my arithmetic, standard formula). The component is about 4.5% of this.
- Polarity needs s = t (a polarity swaps the line and point valencies), so a polarity quotient of a Ree-Tits octagon (s != t) does not exist. The side-swap quotient avoids this. Its loops occur exactly at incident point-line flags, which lowers the degree there (my reasoning).

## Unverified or not opened

- Delorme, "Grands graphes de degré et diamètre donnés", Europ. J. Combin. 6 (1985) 291-302, and "Large bipartite graphs with given degree and diameter", J. Graph Theory (1985): paywalled, not opened. The journal volume is 8 in arXiv:1709.09760 and 9 in arXiv:2406.18994.
- Miller and Širáň, "Moore graphs and beyond", EJC DS14v2 (2013): only the OJS landing page was retrieved (https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS14; `dl/ds14_landing.html`). The file `dl/ds14_survey.pdf` is that HTML page, not the survey. No survey statements are used here.
- Erskine-Tuite journal details (DAM 2018) and the Canale-Gómez bound: taken from secondary citations.
- Araujo-Pardo, Jajcay, Ramos Rivera (submitted 2020), "On a relation between bipartite biregular cages, block designs and generalized polygons": not found.
- Known-to-us items not re-reported: arXiv:2608.03965 and arXiv:2608.27253 (not used as sources).

## Next leads

1. Delorme 1985 (JGT, bipartite; and EJC): check whether the side-swap product is stated for general n-gons, including s != t, and whether octagons are covered.
2. Reference for the Comellas entry "(⊗Q_{2,4})'" at (15,3)=1215: confirm the quotient rule for biregular factors. This is the direct precedent for the octagon version.
3. Full Bachratý dissertation (not the summary): section 5.1 and the Q(5,q) suggestion; check whether his Lemma 2.1.4 diameter argument is the same as the side-swap.
4. References of arXiv:2608.27253 (Isham et al.) for pre-2026 items on biregular factors, as a pointer only.
