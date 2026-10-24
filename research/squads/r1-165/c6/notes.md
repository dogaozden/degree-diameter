# C6 notes: literature and table check (squad r1-165)

Read-only web research by squad-r1-c6-haiku, 2026-10-24 (about 04:40 to 05:15 UTC). No code was run against any graph. The 31,460 count below is by hand. No repo files other than this one were written.

Scratch copies (outside the repo): `/tmp/claude-0/-home-user-degree-diameter/3c73a470-3bbf-5069-a0c3-9333da938358/scratchpad/ds14dl/ds14.pdf` (DS14v2 survey, 92 pp) and `/tmp/claude-0/-home-user-degree-diameter/3c73a470-3bbf-5069-a0c3-9333da938358/scratchpad/ds14dl/ds14survey.txt` (pdftotext output).

## Summary

1. The 27,300 at (Delta, D) = (16, 5) is the CombinatoricsWiki bipartite value as printed in Miller and Siran, "Moore graphs and beyond" (EJC Dynamic Survey DS14, version 2, dated 16 May 2013), Table 4 on p. 37. The caption reads "CombinatoricsWiki, accessed on 10 March 2013". The survey does not say which construction produced that cell. The wiki's colour key and per-cell references are not in the survey, and the wiki was unreachable.
2. No post-2013 bipartite record at (16,5) was found. The live wiki returned HTTP 503 on every attempt, and the Wayback Machine was blocked. The post-2013 bipartite records we did find are at diameter 3, and they beat the 2013 table at Delta = 13 and 15.
3. Isham, Lakhotia, Monroe, Petrini (arXiv:2608.27253 v2) define the bipartite compatibility graph C(k,q), with degree (q+1)^k and diameter 2k+1 (Thm 6.11). For k = 2, q = 3 this gives a 16-regular bipartite graph of diameter 5 and order 2 * [5]_3! / 16 = 31,460. The paper does not compare this with the bipartite table, and does not mention 27,300.
4. The order 31,460 checks out by hand (section Q3). The diameter 5 claim rests on Thm 6.11 and has not been computed.
5. Kronecker-type products of bipartite factors cannot reach 31,460 at (16,5). Two cheap, untested ideas remain (section Ideas).

## Q1: origin of 27,300

- Source: M. Miller and J. Siran, "Moore graphs and beyond: A survey of the degree/diameter problem", Electronic J. Combin. Dynamic Survey DS14, version #DS14v2 (16 May 2013). Table 4 is "The order of the largest known bipartite graphs of maximum degree Delta and diameter D, CombinatoricsWiki, accessed on 10 March 2013."
  - Survey PDF: https://www.combinatorics.org/files/Surveys/ds14/ds14v2-2013.pdf (also https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS14/pdf)
- Row Delta = 16 of Table 4: D=3: 394; D=4: 5,134; D=5: 27,300; D=6: 884,062; D=7: 4,022,340; D=8: 36,201,060; D=9: 288,939,118; D=10: 4,119,507,330.
- D = 5 column, Delta = 3..16: 56, 160, 336, 684, 1,134, 1,710, 2,496, 4,000, 5,850, 8,200, 11,480, 14,760, 20,496, 27,300.
  - Layout check: the first row is Delta = 3 (Heawood 14 at D=3, Tutte 8-cage 30 at D=4, and 80 at (7,3) matches the survey text). The survey text also says the bipartite (3,5) graph of order 56 was found by Bond and Delorme [64] and proved optimal by Jorgensen [216].
- Bipartite Moore bound B(16,5) = 2 * (15^5 - 1)/14 = 108,482. So 27,300 is about 25% of it.
- Construction references in survey section 3.4.4-3.4.5 (p. 36):
  - Bond and Delorme [64, 65]: partial Cayley graphs.
  - Delorme [118, 119]: bipartite *-product and compounding. [119] = C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 8 (1985) 325-334.
  - Loz, Perez-Roses and Pineda-Villavicencio [240] (2012 preprint, "Properties of finite metabelian groups for algebraic constructions") adapted the Loz-Siran voltage method [242] to bipartite graphs. The survey says this "result[ed] in updating more than one third of the table".
  - I could not find [240] online.
- Which construction gives the (16,5) cell is NOT determined. The likely candidates are the Delorme-type products or the [240] lifts. The wiki colour key would settle it.
- Wiki page: https://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs (HTTP 503 on three attempts; Wayback blocked; not in search results).

## Q2: post-2013 changes

- No change at (16,5) was found in any source we could read. The only 2013 snapshot we have is the DS14v2 table above. Its D = 5 column for Delta = 10..16 is 4,000; 5,850; 8,200; 11,480; 14,760; 20,496; 27,300.
- Post-2013 bipartite records, all at D = 3:
  - Araujo-Pardo and Lopez, "On new record graphs close to bipartite Moore graphs", arXiv:2005.02427 (May 2020). Their (q+2)-bipartite family has order 2(q^2+q+5) and diameter 3. Values: q=9 gives Delta 11 and order 190 (matches the 2013 table). q=11 gives Delta 13 and order 274, above the table's 270. q=13 gives Delta 15 and order 374, above the table's 370. The abstract says "improve it at q=11 and q=13".
  - Feria-Puron, Miller, Pineda-Villavicencio, "On large bipartite graphs of diameter 3", Discrete Math. 313 (2013) 381-390, arXiv:1203.3588. D = 3 only.
  - Feria-Puron and Pineda-Villavicencio, arXiv:1010.5651 (defect at most 4). The survey says defect-4 bipartite graphs exist only for D = 3, 4, so this does not affect D = 5.
- Context: the survey lists AAU project "Large bipartite graphs with small diameter" (2008-2010; Jorgensen, Delorme, Miller, Pineda-Villavicencio). It has no table. https://vbn.aau.dk/en/projects/large-bipartite-graphs-with-small-diameter
- 2026 bipartite papers (Isham et al. and Cames van Batenburg-Korsky, below) do not cite or compare with the bipartite table.

## Q3: 2024-2026 papers

### Isham, Lakhotia, Monroe, Petrini, arXiv:2608.27253 ("Kronecker Products, Polarity Quotients and Large Graph Constructions"; submitted 27 Aug 2026, v2 22 Oct 2026)

- https://arxiv.org/abs/2608.27253 ; HTML v2: https://arxiv.org/html/2608.27253v2
- Thm 6.11: "the diameter of C(k,q) is 2k+1". Upper bound attributed to [14, Lemma 2.1]. Lower bound from a rank-function estimate (Lemma 6.10) plus bipartiteness.
- Prop 6.8 and the proof of Thm 1.2: C(k,q) is (q+1)^k-regular. Order is 2 * [2k+1]_q! / (q+1)^k (the summarizer derived this from the proof of Prop 6.16; it agrees with the half-order formula in Cames van Batenburg-Korsky, eq. 6).
- C(2,3): degree 16, diameter 5, order 2 * 251,680 / 16 = 31,460. This beats the table's 27,300.
- Polarity quotient of C(k,q): order [2k+1]_q!/(q+1)^k, degree (q+1)^k, diameter 2k (Thm 1.1). For k=2, q=3 this is a general (16,4) graph with 15,730 vertices.
- Section 7.5, family G6 (generalized hexagon with polarity, q = r = 3): general graph with degree (3+1)(3+1) = 16, diameter 5, order (1+3+...+3^5)^2 = 364^2 = 132,496. This is the previous general (16,5) record (derived, see Mizuno below).
- Table 3 (diameter 3 only, degree up to 20) has no bipartite comparison. Table 2 compares only with H_{k,q}.
- Coverage: I read the full HTML in two passages. Section 7.8.2 and the closing sections were read; no bipartite table appears. The string "27,300" and "31,460" appear nowhere.

### Cames van Batenburg and Korsky, arXiv:2608.03965 ("Asymptotically attaining the Moore bound"; submitted 4 Aug 2026)

- https://arxiv.org/abs/2608.03965 ; HTML v1: https://arxiv.org/html/2608.03965v1
- Defines the halved flag graph H_{k,q} as the even-rank side of the bipartite compatibility graph between P_even(V) and P_odd(V) (section 3). Eq. 6: order [2k+1]_q!/(q+1)^k (= 15,730 for k=2, q=3). Eq. 7: degree at most (q+1)^k((q+1)^k - 1) (= 240). Eq. 8: diameter k (= 2 for k=2).
- Corollary 1.2: the limit is 1 for bipartite graphs (the graphs used are B(H_{k,q}), the bipartite graph with one copy of V on each side).
- It does not state the name C(k,q), the diameter 2k+1, or any (16,5) example.
- So the squad brief's attribution is only partly right. The bipartite compatibility graph is defined in 2608.03965 (implicitly). The name C(2,3), the 16-regular claim and the diameter 5 come from 2608.27253.

### Mizuno, arXiv:2606.15860 (general graphs; submitted 14 June 2026)

- https://arxiv.org/abs/2606.15860
- Abstract: N(12,5) >= 34,992 (previous 29,621) and N(16,5) >= 147,456 (previous 132,496). These are general graphs. The abstract says nothing about bipartite graphs.
- The phrase "controller x route chart" does not appear in the abstract. It appears only in ancillary file names in the summary (route_chart_clean_package, controller_c4xc6_multibase.txt). The abstract says the construction was found through the ChatGPT web interface.
- Wikipedia general table, "as of 14 Oct 2026" and edited 21 Oct 2026: https://en.wikipedia.org/wiki/Table_of_the_largest_known_graphs_of_a_given_diameter_and_maximal_degree
  - N(16,5) = 147,456 (note 24, Mizuno).
  - N(12,5) = 42,342 (note 12, a different 2026 source). Mizuno's 34,992 is therefore not the table's current (12,5) value.
  - N(10,5) = 33,397; N(11,5) = 37,628; N(13,5) = 51,417; N(14,5) = 88,452 (note 24); N(15,5) = 100,000 (note 24).
  - N(14,4) = 8,303; N(15,4) = 11,785 (note 12); N(16,4) = 16,384 (note 28, J. Amarel et al., using URSA).

## Ideas that might transfer to bipartite (16,5)

Ranked by how promising they look. Only the first is already known to beat the table.

1. C(2,3), order 31,460 (Isham et al.). Explicit description, checked by hand:
   - Vertices: even flags W2 < W4 in F_3^5 (lines inside solids of PG(4,3)), and odd flags W1 < W3 (points inside planes).
   - Edges: a complete flag W1 < W2 < W3 < W4 joins its even and odd parts.
   - Counts: lines of PG(4,3) = 1210, each in 13 solids, giving 15,730 even vertices. Points = 121, each in 130 planes, giving 15,730 odd vertices. Total 31,460.
   - Degree: W1 has 4 choices inside W2 and W3 has 4 choices between W2 and W4, so degree 16.
   - Edge count: 15,730 * 16 = 251,680 = number of complete flags of F_3^5.
   - Diameter 5 is the open point. It can be checked by BFS from one even and one odd vertex, because PGL(5,3) acts transitively on each side.
2. Reduced Kronecker product of bipartite factors. Isham Prop 4.15 (as summarized) gives degree Delta_H * Delta_K, diameter max(D_H, D_K), and order |A_H||A_K| + |B_H||B_K|. For balanced factors this is n_H * n_K / 2.
   - Factors (4,5) and (4,5): at most 242^2 / 2 = 29,282, even at the Moore size. Real table factors give 160^2 / 2 = 12,800.
   - Factors C_10 (degree 2, diameter 5) and (8,5): at most 5 * 5,602 = 28,010.
   - Both are below 31,460, and below 27,300 for real factors. Ruled out.
3. Loop cover. If H is (Delta-1)-regular with diameter D on n vertices, the bipartite graph with (x,0) ~ (y,1) iff y is in N_H[x] (closed neighbourhood) is Delta-regular, bipartite, on 2n vertices, with diameter exactly D+1. (My derivation: loops allow lazy walks, so the even and odd distances are the smallest even or odd number at least d_H.)
   - For (16,5): 2 * N(15,4) >= 2 * 11,785 = 23,570. Below 27,300. Ruled out unless a (15,4) graph with at least 15,731 vertices exists.
   - Sanity check on small Moore cases: C_5 gives a 10-vertex (3,3) graph, Petersen gives a 20-vertex (4,3) graph. Both are consistent with the table.
4. Canonical double cover (no loops, untested). For a 16-regular graph H on N vertices with diameter 4, the cover H x K_2 is 16-regular and bipartite on 2N vertices. It beats 31,460 only if N >= 15,731 and the cover has diameter 5.
   - Wikipedia's N(16,4) >= 16,384 would give 32,768 if the cover had diameter 5. That is a long shot. Covers of diameter-D graphs usually have diameter up to 2D+1 = 9, so special structure would be needed.
   - The polarity quotient of C(2,3) (general, 15,730 vertices, degree 16, diameter 4, Isham Thm 1.1) shows the pattern: for a bipartite graph G with polarity, the quotient's double cover (with loops at absolute points) gives back G, and the quotient diameter is at most D(G)-1 (Isham Prop 4.10). I have not checked whether the loopless version behaves the same. Whether the 16,384-vertex graph has such structure is unknown to me.
5. Degree reduction (untested, low prior). Delete a perfect matching from C(2,3). This gives a 15-regular bipartite graph on 31,460 vertices. If the diameter stayed 5, it would beat the 2013 (15,5) entry 20,496. But 31,460 is about 38% of B(15,5) = 82,742, versus about 29% for C(2,3) at Delta = 16, so diameter 6 seems more likely. A BFS test would settle it.

## Not found

- The construction behind the 27,300 cell (no colour key, no per-cell references in the survey, wiki unreachable).
- Any post-2013 bipartite (Delta <= 16, D = 5) entry above 27,300 other than C(2,3) at Delta = 16.
- The Loz, Perez-Roses, Pineda-Villavicencio 2012 preprint (not online via search).
- Any post-2013 update to the bipartite table at D = 5.

## Next check (highest value first)

1. Build C(2,3) explicitly (the flag description above, over F_3), check 16-regularity and bipartiteness, and run BFS from one even and one odd vertex. Two BFS runs on 31,460 vertices settle the diameter. The coordinator's re-check would also need this.
2. Retry https://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs later, to read the current (16,5) cell and its colour-key reference, and to see whether the table has changed since 2013.
3. Test the perfect-matching deletion (idea 5), and the double cover (idea 4) if the 16,384-vertex (16,4) graph can be obtained.
