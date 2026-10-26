# Literature audit, round 2 (table-audit)

Literature sub-agent, 2026-10-26. This adds to LITERATURE.md and does not repeat it. Downloads are in
`sources2/` (see its README for URLs and checksums).

Labels: **[read]** I read the primary source (or the cited pages). **[secondary]** abstract, review, citing work or
database only. **[not reached]** I could not get it. **[inferred]** my arithmetic. **[checked]** I ran a check here.

## Summary

- **New primary sources found.** Two Newcastle PhD theses are open on figshare: H. Pérez-Rosés (2012) and
  R. Feria Purón (2015). Pérez-Rosés was in the bipartite project with Loz and Pineda-Villavicencio. His Table 5.1 is
  the bipartite table, with bold type for the cells the voltage-lift project produced.
- **(13,8) and (16,5):** they are in the table by 2012 and are not bold in Pérez-Rosés's table, so they are not
  from Loz's voltage search. They are green on the wiki (Delorme–Gómez–Quisquater). Pérez-Rosés cites DGQ as
  "unpublished manuscript, 2011". No construction found. Delorme–Gómez 2002 is still **[not reached]**.
- **Loz data:** still lost here. Pérez-Rosés confirms that Loz's thesis and his page held the adjacency lists and the
  voltage assignments. No group list per cell survives in anything I could reach.
- **Small cells:** the upper bounds are Moore − 6 (Feria-Purón–Pineda-Villavicencio). No later paper beats any of the
  five table values. New: the complete census of cubic vertex-transitive graphs (≤ 1280 vertices) shows that **168
  is the largest vertex-transitive bipartite cubic graph of diameter 7, and 506 the largest of diameter 9**. Both
  censuses are complete for those diameters. So (3,7) and (3,9) are optimal among vertex-transitive graphs.

## Q1. Cells (13,8) = 5,314,680 and (16,5) = 27,300

### Who entered them

- **Wiki history [read].** Four revisions: 17 Jan 2012 "CW>Gpineda" (imported from an older install of the wiki),
  3 Jan 2019 Grahame ("1 revision imported"), 30 Mar 2021 Grahame, 18 Feb 2022 Guillermo. Both cells are in the first
  revision, coloured #66ff66 = "Graphs found by C. Delorme, J. Gómez, and J. J. Quisquater", and never changed.
  The import kept one revision only, so nothing older is on this wiki.
  http://combinatoricswiki.org/index.php?title=The_Degree_Diameter_Problem_for_Bipartite_Graphs&action=history
- Gpineda is Guillermo Pineda-Villavicencio. Pérez-Rosés's thesis (§9.1, item 4) says the wiki was set up by Loz,
  Exoo, Pineda-Villavicencio and Pérez-Rosés. **[read]**
- A side detail in revision 296 **[read]**: after the Δ = 10 row the wikitext has a stray line `|- 97 386 380`.
  97,386,380 is the Delorme–Gómez **general** (12,9) value on Comellas's D = 9 page. So the bipartite wikitext was
  edited from a copy of the general table. It is not a bipartite value.
- **Pérez-Rosés, PhD thesis, Univ. Newcastle 2012, §5.3.2 and Table 5.1 [read].**
  https://ndownloader.figshare.com/files/54389441
  - Text: "With the aid of this modified procedure, new record bipartite graphs have been found. ... The entries in
    bold are the ones that have been obtained with the aid of our methods. For more details see [103] and [63];
    there are adjacency lists, the actual voltage assignments used to obtain the graphs, references, etc. Note that
    the values at (14,8) and (15,8) are the same, but the latter can be pushed a little bit further by vertex
    duplication [48]."
  - [103] = Loz's thesis (Auckland 2009). [63] = the Combinatorics Wiki. [48] = "Delorme, C., Gómez, J., and
    Quisquater, J. On large bipartite graphs. unpublished manuscript, 2011." [49] = "Delorme, C., Loz, E.,
    Pérez-Rosés, H., and Pineda-Villavicencio, G. Some properties of metabelian groups for constructing large graphs
    by voltage assignment. in preparation (2012)." (DS14v2 ref. [240] lists the same preprint without Delorme.)
  - I read the font of every cell of Table 5.1 from the PDF (sources2/perez-roses_table5.1_fonts.txt) **[checked]**.
    The bold cells are exactly the 39 orange (Loz) cells of the wiki, no more and no fewer. Every value equals the
    current wiki except (11,3) 186, (13,3) 270, (15,3) 370 (the values before FMP 2013 and Araujo-Pardo–López). So
    the table predates March 2012.
  - (13,8) and (16,5) are not bold. They are not from the voltage-lift search.
- **DS14v2 (2013) [read]:** Table 4 has both values. §3.4.5 does not mention DGQ or Delorme–Gómez 2002 and gives no
  source per cell.
- **Bond–Delorme, Ars Combin. 25C (1988) [secondary: zbMATH review Zbl 0649.05043]:** "A table is presented of best
  known orders if 3 ≤ Δ ≤ 16 and 3 ≤ D ≤ 10 with the corresponding references." That is exactly the range of the wiki
  table, so the wiki table probably descends from Delorme's tables. Ars Combinatoria is not online. **[not reached]**

### The construction: not found

- **Delorme–Gómez, "Some new large compound graphs", EJC 23 (2002) 539–547 [not reached].** pii
  S0195669802905810. The Elsevier API says `openArchiveArticle = true`. Semantic Scholar says a copy is at
  https://core.ac.uk/download/pdf/82826832.pdf. Routes tried:

  | route | result |
  |---|---|
  | doi.org → linkinghub.elsevier.com | JS redirect to ScienceDirect |
  | www.sciencedirect.com (article, /pdf, /pdfft), curl and WebFetch | 403 |
  | reader.elsevier.com | TLS handshake failure at the proxy |
  | api.elsevier.com, view=FULL | 401 "Invalid API Key" (first tries 429) |
  | core.ac.uk/download/pdf/82826832.pdf, core.ac.uk/reader/82826832, curl and WebFetch | 403 (Cloudflare challenge) |
  | api.core.ac.uk v3 | 404 for that id, 429 for others |
  | api.openalex.org | metadata only, no repository copy; later 429 (daily budget used up) |
  | api.unpaywall.org | bronze OA at publisher only |
  | pdfs.semanticscholar.org | 202, empty |
  | scholar.archive.org | bot "verify" page; api.fatcat.wiki connection reset, WebFetch 503 |
  | Google Scholar via WebFetch | no PDF links |
  | ResearchGate | 403 |
  | Comellas mirror papers/ (listed) | not there (9 files, none is DG 2002) |
  | UPCommons (UPC repository) search API | not there |
  | LRI internal reports index (www.lri.fr/~bibli/Rapports-internes/) | only 2005–2008; RR 905 (1994) not online |

- **zbMATH Zbl 1017.05089 [secondary].** Only the abstract: "Using a variation on this classical theme, we build
  some new large graphs and some new large bipartite graphs. We also apply the method of vertex duplication to
  improve some entries in the tables of known large bipartite graphs." MSC 05C75 and **51E12 (generalized quadrangles
  and polygons)**. Its 17 references include Cameron–Thas–Payne, "Polarities of generalized hexagons and perfect
  codes" (1976), Thas, "Circle geometries and generalized quadrangles", J. Bond in the Colloque Franco-Québécois 1991
  proceedings, Bond–Delorme (Ars Combin.), Delorme 1985 EJC and 1992 DAM, Gómez 1990 "Generalized compound graphs".
  It does not cite DGQ. Semantic Scholar's reference list also has Delorme's JGT 1985 paper.
- **Earlier version [secondary, Comellas desc_g9].** "C. Delorme, J. Gomez; Some new large compound graphs. LRI
  Rapport 905 (05/1994)". Its general-graph entries are D = 9 compounds of generalized hexagons: Δ = 11..14,
  orders 48,626,760; 97,386,380; 145,880,280; 194,639,900. Each is 66,430·m with m = 732, 1,466, 2,196, 2,930,
  and 66,430 is the number of points of H(9) **[inferred]**. DS14v2 ref. [127] (Delorme–Quisquater, LRI 317, 1986)
  has the same title.
- **Feria Purón thesis (2015) [read]** and **Pérez-Rosés thesis [read]** say nothing about these two cells beyond the
  table.

### Arithmetic only [inferred]

- (13,8) = 15·|H(11)| = 5·(13,7), where (13,7) = 3·|H(11)| is the tournament compound at the same degree q + 2.
  15 = 5(α+1) with α = 2 in Gómez's ΩB₁ formula N = 5(α+1)N₁. But Ω has Δ = Δ₁ + 2 = 14 for H(11), not 13, and the
  other D = 8 cells use α = ⌊Δ/2⌋ (5, 5, 6, 7, 8 at Δ = 10, 11, 12, 14, 16). So (13,8) is not ΩH₁₁ with the
  thesis's parameters.
- (16,5) = 27,300 is above every (2j+1)·|GQ(q)| at Δ = 16: the best is 9·2,928 = 26,352 (q = 11, j = 4); q = 13,
  j = 2 gives 5·4,760 = 23,800. The gaps (948 and 3,500) are not a Delorme duplication increment that I can see.
  Other factorizations: 10·13·14·15; 25·1,092 (1,092 = |PSL(2,13)|); 15·C(16,4). None is a construction.
- The DG 2002 abstract mentions "vertex duplication to improve some entries in the tables of known large bipartite
  graphs", and its MSC is generalized polygons. A duplication or compound on GQ(q) or H(q) is the likeliest source of
  both cells, but this is a guess.

## Q2. Loz's bipartite data

### What the theses say [read]

- Pérez-Rosés §5.3: the bipartite cells came from Loz–Širáň-style random voltage search over metabelian groups
  H ⋊ψ N (H, N abelian), with extra sieves. Corollary 5.1 (the order of h₁⋯h_k divides the order of the product in
  H ⋊ψ N) gives an a-priori test: if an odd closed walk has H-part of even order, its net voltage has even order. "Some
  more details concerning the sieves and the implementation of the algorithm are given in [103 = Loz's thesis], but
  these particular sieves to get bipartite lifts are not discussed." The base graphs need not be bipartite.
- Feria Purón §3.2.3: "the majority of the non-Moore record graphs in the table are the fruit of the work of Loz and
  Širáň ... Clearly, the lift of a bipartite base graph containing no loops is also bipartite. Loz and Širáň also
  considered other necessary conditions for a lift graph of a non-bipartite graph to be bipartite. ... Loz and Širáň
  only considered groups with a small or trivial center." Also: "Somehow surprisingly, Loz and Širáň were not able to
  beat the previous value 186" at (11,3).
- Neither thesis lists groups, base graphs or voltages per cell.
- Wiki revision 296, External links **[read]**: Loz's page had "adjacency lists for bipartite graphs smaller than
  20,000". The cells below 20,000 among Loz's are (3,9), (4,8), (4,9), (4,10), (5,5), (5,7), (5,8), (6,5), (7,5),
  (8,5), (9,5).

### Routes tried for the data [not reached]

| route | result |
|---|---|
| http://www.eyal.com.au/... | 403 from the proxy ("forbidden by administrative rules") |
| https://www.eyal.com.au/... | parked domain (redirect to /lander) |
| https://www.math.auckland.ac.nz/~eloz002/degreediameter/ | meta refresh to eyal.com.au, nothing else |
| archive.ph / archive.today | 429 captcha page, three tries over several minutes; stopped |
| web.archive.org (curl, WebFetch) | blocked; archive.org availability API 429 |
| Trove / Australian Web Archive (webarchive.nla.gov.au) | Anubis bot wall for curl; WebFetch got only the JS template |
| arquivo.pt CDX 403; Library of Congress (Cloudflare); UK Web Archive 403; archive-it rate limit; Memento TimeTravel 502 | nothing |
| vefsafn.is CDX | empty (no captures) |
| guillermo.com.au (WebFetch) | publications page: no metabelian preprint, no data links |
| Figshare (Deakin, Newcastle) | the two theses above; no Loz data |

For the coordinator (Mac, browser): the repo already used
http://web.archive.org/web/20140125092156/http://eyal.com.au/wiki/The_Degree/Diameter_Problem (reports/live/index.html)
and Wikipedia links https://web.archive.org/web/20160303193729/http://www.eyal.com.au/wiki/The_Degree/Diameter_Problem.
The bipartite page and its adjacency lists should be among the captures listed by
`http://web.archive.org/cdx/search/cdx?url=eyal.com.au/*&fl=timestamp,original,mimetype,statuscode&collapse=urlkey`.
The Australian Web Archive (https://webarchive.nla.gov.au/awa/*/http://www.eyal.com.au/*) needs a JS browser.

## Q3. Small cells: upper bounds, searches, later work

### Upper bounds [read]

- Feria-Purón–Pineda-Villavicencio, DAM 160 (2012), Prop. 6.4, repeated as Props 4.16–4.17 in Feria Purón's
  thesis: "For natural numbers Δ ≥ 3 and 5 ≤ D ≤ 187 (D ≠ 6), N(Δ,D,B) ≤ M(Δ,D,B) − 6" and "For any natural number
  D ≥ 5 (D ≠ 6), N(3,D,B) ≤ M(3,D,B) − 6." The thesis adds: "a bipartite (Δ,D,−5)-graph Γ with Δ ≥ 3 and D ≥ 5
  must be regular and therefore cannot exist". The bound rests on no defect 2 for D ≥ 4 (Delorme–Jørgensen–Miller–
  Pineda-Villavicencio 2009; Pineda-Villavicencio, JACo 2011) and no defect 4 for 5 ≤ D ≤ 187, D ≠ 6 (FPV 2012).
- These are the wiki's upper bounds for all five cells **[read, rev 296]**. I found no lower bound anywhere.

### Cubic vertex-transitive census [read database, checked]

The Potočnik–Spiga–Verret census lists every connected cubic vertex-transitive graph on at most 1280 vertices
(111,360 graphs). MathDataHub serves it with diameter and bipartiteness computed in Sage (J. Vidali):
https://data.mathhub.info/collection/cvt. I queried the largest bipartite graphs per diameter
(sources2/cvt_census/). I decoded the four largest ones myself and ran BFS from every vertex: all are cubic,
bipartite, with the stated diameter and girth.

| D | largest bipartite cubic VT graph (≤ 1280 vertices) | next | census complete for this D? | table |
|---|---|---|---|---|
| 7 | **168** (CVT index 7; girth 12; arc-transitive; Cayley) | 162 | yes: any cubic graph of diameter 7 has ≤ 382 vertices | 168 |
| 8 | 234 (index 2; girth 12; Cayley) | 216 | yes: bipartite Moore bound 510 | 256 |
| 9 | **506** (index 9; girth 14; Cayley; not arc-transitive) | 480 | yes: bipartite Moore bound 1,022 | 506 |
| 10 | 768 (index 2270; girth 12; Cayley) | 720 (Conder's graph) | no: bound 2,046 > 1,280 | 800 |

- So **(3,7) = 168 and (3,9) = 506 are optimal among vertex-transitive bipartite graphs**. A better graph in either
  cell would have to be non-vertex-transitive. Over all cubic VT graphs (bipartite or not) the census maxima for
  D = 2..9 are 10, 14, 30, 60, 82, 168, 300, 546. At D = 7 there are two graphs of order 168 (one bipartite, one of
  girth 9). OEIS A241162 ("largest order of a cubic vertex-transitive graph of diameter d") has the terms
  10, 14, 30, 60, 82, 168, 300, which match D = 2..8 (its stated offset is 3, which looks off by one). **[secondary]**
- The table's (3,8) = 256 and (3,10) = 800 graphs are not vertex-transitive (256 > 234; an 800-vertex VT graph would
  be in the census).
- The census of cubic Cayley graphs up to 5,000 vertices (graphsym.net, 15 GB, sparse6) is complete for bipartite
  Cayley graphs at D = 10 (bipartite Moore bound 2,046). I did not download it. It would show whether any cubic
  bipartite Cayley graph of diameter 10 beats 800.

### Per cell

| cell | table | upper bound (source) | exhaustive or computer bound | later paper beating it |
|---|---|---|---|---|
| (3,7) | 168 | 248 = 254 − 6 (FPV 2012 Prop 6.4; FP thesis Prop 4.17) | none below 248. Optimal among VT graphs (census). | none found |
| (3,9) | 506 | 1,016 = 1,022 − 6 (same) | none below 1,016. Optimal among VT graphs (census). | none found |
| (4,8) | 2,184 | 6,554 = 6,560 − 6 (FPV 2012; FP thesis Prop 4.16) | none | none found |
| (4,9) | 4,970 | 19,676 = 19,682 − 6 (same) | none | none found |
| (6,5) | 684 | 1,556 = 1,562 − 6 (same) | none | none found |

- Origin: (3,9), (4,8), (4,9), (6,5) are bold (Loz project) in Pérez-Rosés's Table 5.1. (3,7) is not bold. The wiki
  credits (3,7) to Conder–Nedela, DGQ and Loz independently, and the census graph is arc-transitive and Cayley, as
  C168.1 in Conder's list.
- Later work checked: Pérez-Rosés, EJGTA 2 (2014) survey **[read]** (no bipartite update); Feria Purón thesis 2015
  **[read]** (only (11,3) = 190); Isham–Lakhotia–Monroe–Petrini, arXiv:2608.27253 (Aug 2026) **[read abstract and
  searched text]** (general graphs; uses Kronecker products of bipartite graphs, no bipartite table values); arXiv API
  searches for "bipartite" with "degree/diameter", "degree-diameter", "bipartite Moore" and title "bipartite" +
  "diameter" (2013–2026): nothing on these cells. Exoo's site (ginger.indstate.edu) did not respond.
- I found no exhaustive search of bipartite graphs for any of the five cells. The orders are far beyond exhaustive
  search. The only complete computer results are the census ones above, and they cover vertex-transitive graphs only.
