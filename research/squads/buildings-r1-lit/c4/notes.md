# c4 notes: follow-ups to arXiv:2608.03965 and arXiv:2608.27253 (searched 2026-10-24, UTC 17:52 to 18:13)

Downloads and raw outputs are in /home/user/degree-diameter/research/squads/buildings-r1-lit/c4/dl/.

## Bottom line
- No source found states (a) (lim n_b/M_b = 1 as a new result), (b) (flag graphs of other building types with diameter = Coxeter number), a new rate, or a new record from flag graphs.
- Follow-ups found: the Wikipedia article (last edited 19:20, 16 Sep 2026), the Lean repo woutercvb/wewantmoore and its issue #1 (opened 18 Sep 2026), and the Kronecker paper's citation record.
- Same-author and adjacent post-Aug 2026 arXiv papers checked by PDF grep: none cites 2608.03965 or 2608.27253.
- The Comellas diameter-5 table (last modified 14 Oct 2026) has 2026 records built from split Cayley hexagon H(9) folds (a G_2 building). They are not described as flag graphs.

## 1. Citers in Semantic Scholar
- Isham, Lakhotia, Monroe, Petrini, "Kronecker Products, Polarity Quotients and Large Graph Constructions", arXiv:2608.27253 (v1 27 Aug 2026; v2 22 Oct 2026). https://arxiv.org/abs/2608.27253
- This is the only citer that Semantic Scholar returns for arXiv:2608.03965 (dl/ss_2608.03965.json). Already read; not a new item.
- Semantic Scholar returns no citations for arXiv:2608.27253 (dl/ss_2608.27253.json: data []). The metadata call returned HTTP 429, so citation counts are not confirmed. The index may lag.

## 2. Wikipedia, "Degree diameter problem" (follow-up that discusses the paper)
- https://en.wikipedia.org/wiki/Degree_diameter_problem. Raw wikitext: https://en.wikipedia.org/w/index.php?title=Degree_diameter_problem&action=raw (dl/wp_raw.wikitext).
- Date of latest edit: "19:20, 16 September 2026" (action=info page, dl/wp_info_page.html).
- Quotes (wikitext, link markup removed):
  - "A 2026 preprint by Wouter Cames van Batenburg and Samuel Korsky reports a proof that, for every fixed positive integer k,"
  - "This resolves a conjecture of Béla Bollobás and shows that, for every fixed diameter, the Moore bound is asymptotically tight as the degree tends to infinity."
  - "Their construction uses regular graphs whose vertices are partial flags in vector spaces over finite fields. The preprint is accompanied by a Lean 4 formalization of its central theorem chain, including the asymptotic theorem."
- Relevance: context only. No (a)-(d) content. No rate or record.

## 3. Lean formalization repo woutercvb/wewantmoore (follow-up; scope statement)
- https://github.com/woutercvb/wewantmoore. README read from https://raw.githubusercontent.com/woutercvb/wewantmoore/main/README.md (dl/gh_raw_readme.md).
- The GitHub API and github.com pages are blocked for this session (HTTP 403), so commit dates and the issue list came only from WebFetch.
- README scope list, verbatim: "The following are outside the kernel-checked scope:" followed by
  - "the explicit `O_k(q⁻¹)` and `O_k(q⁻²)` error rates and the quantitative remark;"
  - "the bipartite-restricted exact limit that uses a separately cited external odd-cycle-free upper bound; and"
- Relevance: (c) names explicit O_k(q^-1) and O_k(q^-2) error rates, which are the paper's rates and not new. (a) is named but no formula is given.
- The paper itself, arXiv:2608.03965 PDF (dl/pdf_2608.03965.txt, lines 112-114): "The graphs used to prove Corollary 1.2 are bipartite. Together with the matching upper bound for odd-cycle-free graphs in [8, Theorem 7], this also shows that the limit is 1 when restricted to bipartite graphs."
- Note: a WebSearch summary said the 2026 result "covers general graphs, not bipartite ones". The paper text above contradicts that.
- README date: it cites "the 4 August 2026 preprint" and "the 3 August 2026 version of the draft". No commit date was readable.

## 4. GitHub issue woutercvb/wewantmoore #1 (follow-up)
- https://github.com/woutercvb/wewantmoore/issues/1. Title: "Asymptotic Moore bound formalization added to Lean Pool". Opened 18 Sep 2026 by Vilin97. Open. No comments visible. Read via WebFetch (summary, not verbatim-checked).
- Body, as relayed by WebFetch: the import was "merged as pull request 444 in the lean-pool repository" at https://github.com/Vilin97/lean-pool/pull/444. WebFetch got HTTP 404 for that PR, so it is unverified.
- Relayed attribution sentence: "The imported proof retains the full theorem and attribution to Wouter Cames van Batenburg, Samuel Korsky," (unverified wording).
- The issue list on the repo shows only this one issue (dated, signed-out view).
- Relevance: none on (a)-(d).

## 5. Largest-known (degree, diameter) table, diameter 5 (Comellas)
- https://web.mat.upc.edu/francesc.comellas/delta-d/desc_g/desc_g5.html (dl/comellas_d5.html; grep verified by curl). Page says "Last modification: October 14, 2026."
- No entry names Cames van Batenburg, Korsky, Isham, Lakhotia, Monroe or Petrini. None is a flag graph or a Kronecker or polarity-quotient construction from the paper's family. The table's rows go up to degree 16, far below the paper's degree cap.
- 2026 building-based entries (not flag graphs; the page does not link them to the paper):
  - "Obtained from the split Cayley hexagon H(9). H(9) has no polarity, but it has dualities of order four." (Rishabh Rajiv, 23 Sep 2026; degree 10, diameter 5).
  - "From a partial fold of the split Cayley hexagon H(9)." (Rajiv, 30 Sep 2026; degrees 11-13 per the WebFetch summary, orders 36563, 41699, 50750, not grep-checked).
  - "Partial fold of the split Cayley hexagon H(9)" entries (Dharunish Yugeswardeenoo, 7 Oct 2026; orders 37628, 42342, 51417 per the WebFetch summary, not grep-checked).
- My identification, not stated on the page: the split Cayley hexagon H(9) is a generalized hexagon, i.e. the G_2 building. The diameter here is 5. The G_2 Coxeter number is 6, and the page makes no Coxeter claim.
- Other 2026 rows are AI-assisted searches with no building link (for example Mizuno, 25 Sep 2026; de Messieres, 5 Oct 2026).

## 6. arXiv scans (API at export.arxiv.org)
- Author search au:Batenburg OR au:Korsky OR au:Isham OR au:Lakhotia OR au:Petrini OR au:Monroe returned 805 hits. Post-Aug 2026 items by these authors:
  - 2608.23260, Cames van Batenburg, Goedgebeur, Jooken (24 Aug 2026), "Counterexamples to the Albertson-Berman conjecture: minimum order, connectivity and an improved ratio bound". PDF grep: no match for 2608.03965, Moore bound or flags.
  - 2609.15596, Cames van Batenburg, Claus, Joret, Petit, Raymond, Robinson (14 Sep 2026), "An improved bound on the treewidth of planar graphs excluding a grid minor". Grep negative.
  - 2609.07196, Korsky (7 Sep 2026), "A Resolution of the de Bruijn-Erdos Consecutive-Gap Problem". Grep negative.
  - 2610.14037, Korsky (2 Oct 2026), "Sharp Antipode-Neighbor Bounds in Every Dimension". Grep negative; its only Korsky self-citation is arXiv:2603.10334.
- Moore-bound and degree-diameter items after Aug 2026 (abstract level, PDFs grep-checked for citations):
  - 2608.12425, Shallcross (12 Aug 2026), "On the Total Regularity of Almost Mixed Moore Graphs". Grep negative.
  - 2608.08997, Kaur and Kumar (10 Aug 2026), "A proof of the cyclotomic conjecture and the non-existence of almost Moore digraphs". Grep negative.
  - 2610.04815, Stankovski Wagner (3 Oct 2026), "Less is Moore" (diameter-2 Moore graphs). Grep negative.
- Flag-titled items after Aug 2026, unrelated to degree-diameter: 2610.06081 (5 Oct 2026, point-hyperplane incident flags and off-diagonal Ramsey graphs) and 2610.22902 (16 Oct 2026, triangle-free rank-Ramsey graphs from ordered incidence lifts).
- math.CO scan: cat:math.CO with submittedDate 1 Aug to 24 Oct 2026 returned 3551 hits. Only the newest 1000 (1 to 22 Oct 2026) were keyword-scanned. Titles for flag, building, bipartite, Coxeter and Moore show no flag-graph or degree-diameter paper. The rest (about 2550 entries from Aug and Sep) is not covered. The arXiv listing pages failed (HTTP 400 for show=3000), so the API was used instead.

## 7. Searches with no further follow-up
- WebSearch on the title plus authors: Wikipedia and the arXiv PDF only.
- WebSearch on the Kronecker title: only arXiv:2608.27253.
- WebSearch on halved flags and Coxeter number: nothing about other building types. Hits on Coxeter graphs are unrelated.
- WebSearch on the bipartite limit: nothing that restates lim n_b/M_b = 1 outside the paper.
- Semantic Scholar: one citer, no others.
- No blog post, talk or other repo found.

## Gaps
- Semantic Scholar metadata rate-limited (429). math.CO Aug-Sep 2026 not scanned. Lean Pool PR 444 unverified (404). github.com issues and API blocked, so only WebFetch relays were available.
