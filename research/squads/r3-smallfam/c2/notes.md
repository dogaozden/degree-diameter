# c2 literature notes (round r3-smallfam, 2026-10-25)

Question: who constructed the open bipartite cells (3,10) 800 and (3,7) 168, and does any post-2012 bipartite (Delta, D) result beat the CombinatoricsWiki bipartite table at (3,7) 168, (3,9) 506, (3,10) 800, (4,8) 2184, (4,9) 4970?

Short answer: the five values are the wiki bipartite values as of 10 March 2013. No source I read credits (3,10)=800 or (3,7)=168 to anyone. No post-2012 bipartite result I could read beats any of the five cells. The live wiki page returned HTTP 503 on every attempt, so the beat-check is against the 2013 snapshot only.

Quote tags: [pdftotext] = exact text extracted locally from a PDF with pdftotext. [WebFetch] = model-extracted summary from WebFetch, not byte-verified. UNVERIFIED = not read by me.

## 0. Access log
- https://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs and the http:// form: HTTP 503 on all 4 attempts. Not read.
- https://www.sciencedirect.com/science/article/pii/S0012365X10004115: HTTP 403. Not pursued. Title only, from a search result (UNVERIFIED): "Large bipartite Cayley graphs of given degree and diameter" (2010, pre-2012).
- Survey and two arXiv PDFs were returned as raw bytes by WebFetch. I ran pdftotext on the saved copies (no code from them was run). Extracted texts are in /tmp/claude-0/-home-user-degree-diameter/b0dda455-de6a-56ff-a7ef-af02eb599aa1/scratchpad/ (ds14txt/ds14v2.txt, kron2026/kron.txt, comellas95/nlarge.txt).

## 1. The five cells are the wiki bipartite values of March 2013
Source: E. Miller and J. Širáň, "Moore graphs and beyond: A survey of the degree/diameter problem", Electron. J. Combin. DS14v2 (2013), https://www.combinatorics.org/files/Surveys/ds14/ds14v2-2013.pdf, Table 4 (p. 37) [pdftotext]:
- Caption, exact: "Table 4: The order of the largest known bipartite graphs of maximum degree ∆ and diameter D, CombinatoricsWiki, accessed on 10 March 2013."
- Row ∆=3 for D=3..10: 14 30 56 126 168 256 506 800. Row ∆=4: 26 80 160 728 840 2 184 4 970 11 748.
- So (3,7)=168, (3,9)=506, (3,10)=800, (4,8)=2184, (4,9)=4970. These match the brief.

Bipartite Moore bound (survey: Biggs; formula B = 2((∆-1)^D - 1)/(∆-2) for ∆>2, which reproduces the survey's own values 14, 30, 126 and 56 = B_{3,5}-6). Ratios are my arithmetic:
- (3,7): 168/254 = 0.661. (3,9): 506/1022 = 0.495. (3,10): 800/2046 = 0.391. (4,8): 2184/6560 = 0.333. (4,9): 4970/19682 = 0.253.
- Observation only: the value 800 also appears as (8,4), and there it equals B_{8,4} = 800 exactly. The survey says "For D = 3, 4 and 6, whenever ∆ − 1 is a prime power, the value of b∆,D equals B∆,D" [pdftotext], and 7 is a prime power. So the repeated 800 is not a copying error in the table I can see, but the (3,10) cell still has no documented source.

## 2. Who built (3,10) 800 and (3,7) 168: not documented in any source I read
- The survey does not attribute 800 or 168 in its bipartite section. It attributes only these bipartite entries: "The value of b3,5 corresponds to an optimal bipartite graph of degree 3, diameter 5 and order 56 found by Bond and Delorme [64], whose optimality was proved by Jørgensen [216]." and "A bipartite graph of order b7,3 = 80 was independently constructed by Hafner and Loz, and its optimality was settled by Feria-Purón, Miller, and Pineda-Villavicencio [152]." [pdftotext]
- Methods credited: "Bond and Delorme [64, 65] gave new constructions of large bipartite graphs with given degree and diameter, using their concept of a partial Cayley graph. Other constructions of large bipartite graphs were found by Delorme [118, 119], using bipartite versions of operations described earlier, most notably, ∗-product and compounding." [pdftotext]
- Table update: "Loz, Pérez-Rosés and Pineda-Villavicencio [240] adapted the voltage-assignment-based method developed by Loz and Širáň [242] for general graphs to the case of bipartite graphs; this resulted in updating more than one third of the table of the largest known bipartite graphs." [pdftotext]. Its reference: "[240] E. Loz, H. Pérez-Rosés, and G. Pineda-Villavicencio, Properties of finite metabelian groups for algebraic constructions, (2012) preprint." [pdftotext]. This is the likeliest origin of many 2013 bipartite cells. That it produced these five cells is UNVERIFIED.
- Delorme's bipartite paper: C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9 (1985) 325–334, https://doi.org/10.1002/jgt.3190090304. Survey ref [119] has this title [pdftotext]. The reference is also on https://web.mat.upc.edu/francesc.comellas/old-files/delta-d/table_degree_diameter.html [WebFetch]. Metadata via https://api.openalex.org/works/doi:10.1002/jgt.3190090304 [WebFetch]: single author C. Delorme, vol. 9 no. 3, pp. 325–334. I did not read the article (UNVERIFIED content).
- Bermond–Delorme–Quisquater references in the survey: [47] "Ann. Discrete Math. 17 (1982) 65–73"; [48] "Information Processing Letters 15 (1982) 10–13"; [50] "Tables of large (∆, D)-graphs, Discrete Applied Mathematics 37/38 (1992) 575–577"; [51] Parallel and Distributed Computing 3 (1986). Also [127] "C. Delorme and J.J. Quisquater, Some new large compound graphs, Internal Report 317, LRI, December 1986." None of these has Gómez as an author.
- "Delorme, Gómez, Quisquater, On large bipartite graphs": not found. Searches returned no such title or author triple. Treat as UNVERIFIED.
- Who maintained the tables in 1995: "An updated version of these tables is available from J-C Bermond and C. Delorme (e-mail: cd@lri.fr)." [pdftotext of Comellas & Gómez, https://web.mat.upc.edu/francesc.comellas/old-files/nlarge/nlarge_f.pdf]. This sentence follows the general (∆,D) table in that paper. Whether it covers the bipartite table is unknown.
- Quisquater's technique as described there: "The technique is a generalization of a method used by Quisquater [16], based on the replacement by a complete graph of a single vertex from a bipartite Moore graph." [pdftotext]. That paper is about general graphs, mainly diameter 6.

Conder–Nedela 168: not found.
- The survey never mentions Nedela (grep: 0 hits). Conder appears only as [109]: "M. Conder, Trivalent (cubic) symmetric graphs on up to 2048 vertices, http://www.math.auckland.ac.nz/conder/symmcubic2048list.txt (2006)." [pdftotext]
- The Comellas resource page (https://combgraph.upc.edu/en/resources) links that file with the text "Marston Conder, salmon: August 17, 2006 (3,10) [Co06]." [WebFetch]. I read this as a general-graph table credit (UNVERIFIED reading).
- Search result titles only (UNVERIFIED, content not read): Conder & Nedela, "Symmetric cubic graphs of small girth" (JCTB 2007) and "A refined classification of symmetric cubic graphs" (J. Algebra 2009). No snippet mentions diameter 7 or 168 vertices. A cubic 168-vertex bipartite graph could plausibly come from a symmetric cubic classification, but that is speculation.

## 3. Post-2012 bipartite results against the five cells
None beats the five cells in what I read.
- arXiv:1203.3588, Feria-Purón, Miller, Pineda-Villavicencio, "On large bipartite graphs of diameter 3" (submitted 15 Mar 2012; Discrete Math. 313(4) (2013) 381–390 per survey ref [152]). Diameter 3 only. [WebFetch, not verbatim]: the abstract states orders 80 (degree 7) and 190 (degree 11), both at diameter 3. Not a cell.
- arXiv:2005.02427, Araujo-Pardo and López, "On new record graphs close to bipartite Moore graphs" (submitted 5 May 2020). Diameter 3 only. [WebFetch, not verbatim]: "These graphs attain the record value for q=9 and improve the values for q=11 and q=13." Not a cell.
- arXiv:2608.27253v2 (22 Oct 2026), Isham, Lakhotia, Monroe, Petrini, "Kronecker Products, Polarity Quotients and Large Graph Constructions" [pdftotext of https://arxiv.org/pdf/2608.27253]:
  - Abstract, exact: "Kronecker products of these polarity quotients give another new family of graphs of diameters 2, 3 and 5, including a diameter-3 degree-18 graph of order larger than any previously known for that degree and diameter."
  - Theorem 1.1, exact (exponent of k lost in extraction, the text elsewhere gives (q+1)^k): "the bipartite compatibility graph C(k, q) admits a polarity β, and its polarity quotient graph Pβ (C(k, q)) has diameter 2k and degree (q + 1)k."
  - The bipartite compatibility graphs C(k,q) are cited to [14] = W. Cames van Batenburg and S. Korsky, arXiv:2608.03965 (2026). I did not read [14] (UNVERIFIED).
  - Theorem 6.11, exact: "Then the diameter of C(k, q) is 2k + 1." The text also says C(k,q) is "(q+1)k -regular" (exponent lost in extraction; (q+1)^k), so it is bipartite with degree (q+1)^k and diameter 2k+1.
  - Consequence: degree 3 or 4 needs k=1 (q=2 gives degree 3, q=3 gives degree 4). Those cases have diameter 3 (the projective-plane incidence graphs, 14 and 26 vertices). For k ≥ 2 the degree is at least 9. So this family cannot hit (3,7), (3,9), (3,10), (4,8) or (4,9). The polarity quotients have even diameter 2k and degree (q+1)^k, and they are not bipartite (the paper's own quotients generalize Erdős–Rényi–Brown polarity graphs).
- Wiki-date claims from the search summaries, checked:
  - "the wiki's degree-diameter table was last refreshed in 2022": not supported. The only 2022 wiki reference in the 2026 paper is its ref [34]: "E. Loz, H. Pérez-Rosés, and G. Pineda-Villavicencio. The degree-diameter problem for general graphs. http://www.combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_General_Graphs, 2022. Accessed 20 May 2026." [pdftotext]. That is the general-graphs page.
  - "header dates it to January 2012": UNVERIFIED, not read.
- Pre-2013 items, for context only: Feria-Purón and Pineda-Villavicencio, "On bipartite graphs of defect at most 4", Discrete Appl. Math. 160 (2012) 140–154 (survey ref [154]). The catalogue covers defect ≤ 4 only. (3,7) has defect 254−168 = 86, so it does not apply. Bond & Delorme, Ars Combin. 25C (1988) 123–132 (survey ref [64]).

## 4. Caveats and next steps
- Coverage: 4 failed attempts at the live wiki bipartite page, and the bipartite literature searches were not exhaustive. The "no beat" conclusion is medium-low confidence.
- Next, for the main session:
  1. Re-read the live CombinatoricsWiki bipartite table when it returns (503 here) and compare the five cells and their reference column with the 2013 values above.
  2. Check Delorme 1985 (JGT 9: 325–334, DOI above) and Bond–Delorme 1988 for the (3,10) and (3,7) constructions. Check Cames van Batenburg–Korsky arXiv:2608.03965 if its bipartite families reach degree 3 or 4 beyond k=1.
  3. Treat the "Delorme, Gómez, Quisquater" and "Conder–Nedela" attributions as unverified.
