# c8 (wildcard): live tables and metadata sweep

Date accessed for every source below: 2026-10-24 (UTC clock 17:53 to 18:08 for this card).
Approach: (a) live tables (CombinatoricsWiki bipartite and general, Wikipedia general table, Comellas arXiv table), plus (b) zbMATH Open and MathOverflow search pages. Thesis search (c) gave leads only; the hosts did not load. Downloads are in `c8/dl/`; parsing scripts are in `c8/tools/` (stdlib only, run with `python3 -I`).

## Headline
- The CombinatoricsWiki bipartite table has no entry attributed to flags, buildings, Coxeter groups, polarity or Kronecker products, or to 2026 papers. Its page was last modified on 18 February 2022.
- The general-table cells disagree across three sources. The Wikipedia copy, "as of 14 October 2026", attributes its differing cells to 2026 AI-assisted searches. None of this is checked beyond the arXiv abstract for Mizuno (2606.15860).
- The zbMATH Open record for arXiv:2608.27253 lists different authors from the arXiv metadata. The arXiv metadata matches the brief (Isham, Lakhotia, Monroe, Petrini).
- MathOverflow returned nothing relevant. math.stackexchange was not searched.

## 1. Bipartite live table (CombinatoricsWiki)
- URL: http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs (curl HTTP 200, 50,806 bytes; saved as `c8/dl/cw_bip_http.html`).
- TLS note: the https URL fails verification (curl error 60, "unable to get local issuer certificate"), even with `--cacert /root/.ccr/ca-bundle.crt`. WebFetch on the https URL returned HTTP 503. Verification was not disabled; the http copy was used.
- Page text: "Below is the table of the largest known bipartite graphs (as of January 2012) in the undirected degree diameter problem for bipartite graphs of degree at most 3 <= d <= 16 and diameter 3 <= k <= 10."
- Footer: "last modified on 18 February 2022, at 05:55." The "2026" strings in the HTML are only the parser-cache timestamp (`20261023194539`, revision id 649), not content.
- Keyword scan of the page (flag, building, Coxeter, polarity, Kronecker, Cames, Isham, Korsky, Lakhotia, Monroe, Petrini): no hits.
- Quote, Feit and Higman: "Feit and Higman, and also independently Singleton, proved that such graphs exist only when the diameter is 2,3,4 or 6."
- Colour legend, exact text:
  - #bbffff: "Bipartite Moore graphs (optimal)."
  - #CC6600: "Graph duplications found by C. Delorme and G. Farhi."
  - #66ff66: "Graphs found by C. Delorme, J. Gómez, and J. J. Quisquater."
  - #0066CC: "Optimal graph found by R. Bar-Yehuda and T. Etzion and by J. Bond and C. Delorme."
  - #993300: "Graph found independently by M. Conder and R. Nedela., by C. Delorme, J. Gómez, and J. J. Quisquater and by Eyal Loz."
  - #ff0000: "Graphs found independently by Paul Hafner and by Eyal Loz."
  - #FF9900: "Graphs found by Eyal Loz as part of the joint project The degree/diameter problem for several classes of graphs by E. Loz, H. Pérez-Rosés and G. Pineda-Villavicencio."
  - yellow: "Graphs found by R. Feria-Puron, M. Miller and G. Pineda-Villavicencio and independently by G. Araujo and N. López."
  - pink: "Graphs found by G. Araujo and N. López."
- Upper-bound legend: Moore bound, "Moore bound minus 2", "Moore bound minus 6".

Current values, D = 5 and D = 8, Delta = 3 to 16 (best known order; colour; nested "upper bound ; ratio" from the page's second table):

| Delta | D=5 best | colour / finder | D=8 best | colour / finder |
|---|---|---|---|---|
| 3 | 56 | #0066CC, Bar-Yehuda & Etzion; Bond & Delorme (optimal) | 256 | #66ff66, Delorme, Gómez, Quisquater |
| 4 | 160 | #ff0000, Hafner; Loz | 2184 | #FF9900, Loz et al. joint project |
| 5 | 336 | #FF9900 | 9234 | #FF9900 |
| 6 | 684 | #FF9900 | 29790 | #FF9900 |
| 7 | 1134 | #FF9900 | 80940 | #FF9900 |
| 8 | 1710 | #FF9900 | 201480 | #FF9900 |
| 9 | 2496 | #FF9900 | 449480 | #FF9900 |
| 10 | 4000 | #66ff66 | 1176480 | #66ff66 |
| 11 | 5850 | #66ff66 | 2246940 | #66ff66 |
| 12 | 8200 | #66ff66 | 4650100 | #66ff66 |
| 13 | 11480 | #66ff66 | 5314680 | #66ff66 |
| 14 | 14760 | #66ff66 | 14172480 | #66ff66 |
| 15 | 20496 | #66ff66 | 14172480 | #66ff66 |
| 16 | 27300 | #66ff66 | 36201060 | #66ff66 |

- Upper bounds from the same page (nested table, value ; ratio as printed): D=5: Delta=3 56 (100%), 4: 236 (67.79%), 5: 676 (49.70%), 6: 1556 (43.95%), 7: 3106 (36.50%), 8: 5596 (30.55%), 9: 9356 (26.67%), 10: 14756 (27.10%), 11: 22216 (26.33%), 12: 32204 (25.46%), 13: 45236 (25.37%), 14: 61876 (23.85%), 15: 82736 (24.77%), 16: 108476 (25.16%). D=8: Delta=3 504 (50.79%), 4: 6554 (33.32%), 5: 43684 (21.13%), 6: 195306 (15.25%), 7: 671840 (12.04%), 8: 1921594 (10.48%), 9: 4793484 (9.37%), 10: 10761674 (10.93%), 11: 22222216 (10.11%), 12: 42871770 (10.84%), 13: 78178484 (6.79%), 14: 135955114 (10.42%), 15: 227044464 (printed as 0%), 16: 366127226 (9.88%).
- Upper bounds are consistent with Moore-minus-defect values (for example, 504 = 510 - 6 for Delta=3, D=8, with Moore 2((d-1)^D - 1)/(d-2) = 510).
- Flags on this table (not verified further):
  - (15,8) ratio is printed as 0%, but 14172480/227044464 = 6.24%.
  - (14,8) and (15,8) are both 14172480, which may be a copy error.
- Attribution check: the only finders named are those in the legend above. None is flags, buildings or 2026.

## 2. General live tables (requested cells)
Sources:
- CombinatoricsWiki general table: http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_General_Graphs (curl HTTP 200; `c8/dl/cw_general_http.html`). Last modified 18 February 2022, at 05:43 (revision 646). Intro: "Below is the table of the largest known graphs (as of September 2009)".
- Wikipedia: https://en.wikipedia.org/wiki/Table_of_the_largest_known_graphs_of_a_given_diameter_and_maximal_degree (curl via CA bundle, HTTP 200; `c8/dl/wiki_general_table.html`). Text: "Below is the table of the vertex numbers for the best-known graphs (as of 14 October 2026)". Footer: "This page was last edited on 21 October 2026, at 14:01". Degrees 3 to 16 only.
- Comellas, arXiv:2406.18994v2 (PDF text: "arXiv:2406.18994v2 [math.CO] 24 Jan 2026"; https://arxiv.org/abs/2406.18994; `c8/dl/arxiv_2406_18994.pdf`). Table 1 caption: "Table 1: Largest (∆, D)-graphs (January 2026). In bold new results since the publication of the 2013 survey [29]." Text: "Table 1 gives the current state of the art for degrees up to sixteen and diameter up to ..." (no degree 18).

| (Delta, D) | CombinatoricsWiki general (rev 646, 2022) | Comellas arXiv v2 (Jan 2026) | Wikipedia (as of 14 Oct 2026) |
|---|---|---|---|
| (9,4) | 1 550 (#FF9900, "Graphs found by E. Loz") | 1 640 (Table 2: "Z40 ⋊24 Z41") | 1 765 [note 22] |
| (16,4) | 14 640 (#cccccc, "Graphs found by J. Gómez and M. A. Fiol") | 14 640 | 16 384 [note 28] |
| (15,7) | 8 599 986 (#FF9900, Loz) | 8 599 986 | 9 758 988 [note 6] |
| (15,3) | 1 215 (#81BEF7, "Graphs found by C. Delorme") | 1 215 | 1 539 [note 14] |
| (18,3) | 1 620 (#ff6600, "Graphs found by E. Loz and G. Pineda-Villavicencio") | not in table (Delta <= 16) | not in table (Delta <= 16) |

CombinatoricsWiki upper bounds (nested): (9,4) 5265 (29.43%); (16,4) 57856 (25.30%); (15,7) 121630965 (7.07%); (15,3) 3165 (38.38%); (18,3) 5526 (29.31%).

Wikipedia notes for those cells, exact text as extracted (2026 attributions unverified unless marked):
- [22] "Graph found by Francesc Comellas in 2026 with OpenAI GPT-6.1 Sol assistance."
- [28] "Graph found by J. Amarel, N. DeBardeleben, M. Grosskopf, V. Job, E. Lawrence, L. Monroe, and R. Somasundaram in 2026 using URSA (an agentic tool )."
- [6] text ends "Bhakar in 2026 with Claude Fable assistance." (leading words not recovered).
- [14] "Graphs found by Rishabh Rajiv in 2026 using agentic coding systems."
- Other 2026 notes on the same page (not mapped to my cells): [15] "Graphs found by Rithwik Gupta in 2026 with AI-assisted computational searches."; [17] "Graphs found by Michel de Messieres in 2026 with Claude assistance."; [24] "Graphs found using ChatGPT by Mizuno (2026)."; [26] "Graph found in 2026 by anonymous person."
- Older notes on the same page: [7] "Graph found by Jianxiang Chen in 2018."; [8] "Graph found by Geoffrey Exoo in 2010."

Mizuno preprint, checked on its arXiv abstract page (https://arxiv.org/abs/2606.15860, fetched 2026-10-24): title "New lower bounds for the degree/diameter problem via interaction with a browser-accessible LLM", author Mizuno, Ryosuke, subject math.GM. Abstract: "...showing that N(12,5) >= 34,992 and N(16,5) >= 147,456." Matches Wikipedia (16,5) = 147 456 [note 24]. Wikipedia's (12,5) is 42 342, which is larger than 34,992; its source (note 12) was not recovered. Unverified: the models named in the notes (GPT-6.1 Sol, Claude Fable), and the claimed finders.

Comellas Table 2 entry (9,4): "(9, 4) 1 640 Z40 ⋊24 Z41 [25,28],[14,40],[29,11],[39,12],[20,35]" (arXiv:2406.18994v2, PDF text).

## 3. zbMATH and MathOverflow (approach b)
- zbMATH Open search https://zbmath.org/?q=bipartite+degree+diameter+Moore+bound (curl HTTP 200; `c8/dl/zbmath_search.html`). Records seen (abstracts not opened, so content is unverified):
  - Zbl 1492.05123, "On new record graphs close to bipartite Moore graphs.", Graphs Comb. 38, No. 4, Paper No. 110, 14 p. (2022). Authors: Cioaba, Sebastian M.; Koolen, Jack H.; Mimura, Masato; Nozaki, Hiroshi; Okuda, Takayuki. Pre-2026 lead for the bipartite near-Moore question.
  - Zbl 1571.05032, "On bipartite biregular large graphs derived from difference sets.", J. Graph Theory 110, No. 2, 174-181 (2025). Authors begin: Dalfó, Cristina; Erskine, Grahame; Exoo, Geoffrey; Fiol, Miquel Àngel; Tuite, James; the list is truncated in my extraction.
  - Zbl 1569.05056, "On bipartite biregular Moore graphs.", Discrete Mathematics Days 2022 (DMD20/22), pp. 274-279 (2022). Author not extracted.
  - arXiv:2608.27253 record, zbMATH authors: "Araujo-Pardo, Gabriela ; Dalfó, Cristina ; Fiol, Miquel Àngel ; López, Nacho". CONFLICT: the arXiv abstract page for 2608.27253 (https://arxiv.org/abs/2608.27253, date 2026/08/27) lists "Isham, Kelly; Lakhotia, Kartik; Monroe, Laura; Petrini, Fabrizio". Treat the zbMATH authorship for that record as wrong until checked. Title and identifier match.
  - arXiv:2608.27253 abstract (arXiv, verified): "...construct new families of graphs, all of which have orders that asymptotically approach the Moore bound." (known paper; not re-reported.)
- MathOverflow search https://mathoverflow.net/search?q=bipartite+degree+diameter+Moore (curl HTTP 200; `c8/dl/mo_search.html`): one result, question 100265, "Not especially famous, long-open problems which anyone can understand". Unrelated. No MathOverflow thread found.
- math.stackexchange: not searched (time box).

## 4. Theses and talks (approach c): leads only
- WebSearch surfaced a University of Newcastle repository record (https://nova.newcastle.edu.au/vital/access/manager/Repository/uon:19143) and an Auckland record (https://researchspace.auckland.ac.nz/handle/2292/52008). Neither host loaded: WebFetch gave ENOTFOUND for Newcastle and an empty page for Auckland; curl gave HTTP 000 for both. Content unverified, including the search summaries that mention bipartite pairs.
- ICMS 2023 Comellas talk ("IWONT2023-Comellas_60years_deg_diam.pdf"): WebFetch gave EAI_AGAIN for www.icms.org.uk; curl on the IWONT_Comellas.pdf path gave "CONNECT tunnel failed, response 502". Not read.
- Feria-Purón slides (`c8/dl/puron_talk.pdf`, "On the Degree/Diameter Problem for Graphs Embedded on Surfaces", talk dated July 31, 2013): general overview, no 2026 content, low value.

## 5. Verified pre-2026 source (approach a/c crossover)
- Comellas and Gómez, "New Large Graphs with Given Degree and Diameter", in Graph Theory, Combinatorics and Algorithms vol. 1 (Alavi and Schwenk, eds.), Wiley, 1995, pp. 221-233. URL: https://web.mat.upc.edu/francesc.comellas/old-files/nlarge/nlarge_f.pdf (saved as `c8/dl/comellas_nlarge_f.pdf`; text in `c8/dl/comellas_nlarge_f.txt`).
  - Abstract, exact: "The graphs are constructed from Moore bipartite graphs by replacement of some vertices by adequate structures."
  - Exact: "For bipartite graphs, by counting arguments it is easy to obtain the following upper bound (see [5]) for the maximum order of a (∆, D) graph" with b(∆,D) <= 2((∆-1)^D - 1)/(∆-2) for ∆ > 2 (formula reconstructed from the PDF text layer).
  - Exact: "They exist only for D = 2 (complete bipartite graphs K∆,∆) or D = 3, 4, 6. For these values of D, bipartite Moore graphs exist if ∆ - 1 is a prime power."
  - This is a counting bound. It is not an asymptotic attainment statement, so it does not meet the score-3 criterion.

## 6. Unverified leads (WebSearch summaries only, not opened)
- arXiv:2310.12137 (Araujo-Pardo, Kiss, Szőnyi, "A little more about bipartite biregular cages, block designs, and generalized polygons"): summary says it treats equality at the bipartite Moore bound for biregular graphs. Unverified.
- arXiv:1203.3588 ("On large bipartite graphs of diameter 3") and arXiv:2404.04680 / arXiv:2403.18943: summaries only. Unverified.
- arXiv:1805.01056 (spectral Moore problem for bipartite regular graphs): summary says it "suspects" a diameter >= 5 extremal characterisation. Unverified.

## 7. Failures (for the coordinator)
- https://combinatoricswiki.org: TLS verification failure with the proxy CA bundle; WebFetch 503. Used http.
- https://www.icms.org.uk/... : DNS failure in WebFetch; curl CONNECT 502.
- nova.newcastle.edu.au, researchspace.auckland.ac.nz: not reachable (see section 4).
- The proxy status lists recent 502s for mcp.uk.definely.com. Not related to this card's sources.
