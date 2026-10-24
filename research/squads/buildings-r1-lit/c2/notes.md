# c2 notes: Delorme 1985 and the lim sup question for D=7 (general) and D=8 (bipartite)

Card c2, literature direction C. Downloads are in `dl/` in this folder. Time box exceeded (about 35 min).

## Bottom line

- No pre-2026 source found that states lim sup n(Δ,7)/Δ^7 = 1, or the bipartite lim sup n_b(Δ,8)/M_b(Δ,8) = 1.
- The most explicit pre-2026 statement (Bachratý–Šiagiová–Širáň 2017) lists the diameters with lim sup = 1 as k in {2,3,5} only. For k=7 it gives only a lower bound of about 0.0425.
- The 2013 survey says µ_D (liminf) is "unknown" for every D outside {1,2,3,5}.
- The EJC 1985 full text was NOT read. ScienceDirect returns a Cloudflare error for this proxy IP, so everything about its content is second-hand and marked as such.
- Our own hand check (section 5, not literature, not computer-verified): the Delorme-type operations (tensor component, then polarity quotient) applied to the GO(q,q²) incidence graph would give lim sup 1 for D=7 and for bipartite D=8. The secondary sources do not mention octagons at all.

## 1. Bachratý, Šiagiová, Širáň, "Asymptotically approaching the Moore bound for diameter three by Cayley graphs", arXiv:1709.09760 (v1, 27 Sep 2017)

- URL: https://arxiv.org/abs/1709.09760 (PDF: https://arxiv.org/pdf/1709.09760). Authors per PDF header: M. Bachratý, J. Šiagiová, J. Širáň.
- Location: Introduction, pp. 1–2.
- Quotes (exact, pdftotext rendering):
  - (i) p. 1: "the problem of Delorme [6] of determining the value of lim sup_{d→∞} n(d, k)/d^k = lim sup_{d→∞} n(d, k)/M(d, k) for every fixed k ≥ 2."
  - (ii) p. 2: "The best available result addressing Delorme's problem is his own observation [6] that lim sup_{d→∞} n(d, k)/M(d, k) = 1 for k ∈ {2, 3, 5}. This follows by taking polarity quotients of the incidence graphs of generalised n-gons admitting a polarity (cf. [17]) for n ∈ {3, 4, 6}, respectively."
  - (iii) p. 2: "For the remaining diameters the best currently known results on Delorme's problem are much weaker but far from easy to prove. We know that lim sup_{d→∞} n(d, 4)/M(d, 4) ≥ 1/4 by [7], and from [4] we have lim sup_{d→∞} n(d, k)/M(d, k) ≥ (1.6)^{−k} for k ≥ 6, where 1.6 can be replaced by 1.57 for k ≡ −1, 0, 1 mod 6."
- References: [6] C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 8 (1985) 325–334. [7] C. Delorme, "Examples of products giving large graphs with given degree and diameter", Discrete Appl. Math. 37/38 (1992) 157–167. [4] E. A. Canale and J. Gómez, "Superfluous edges and exponential expansions of de Bruijn and Kautz digraphs", Discrete Appl. Math. 138 (2004) 303–331.
- Answers:
  - (a) Which D were asymptotically Moore as of 2017: k in {2,3,5}, credited to Delorme's own observation in [6], the JGT paper. Not to the EJC paper.
  - (a) D=7 is not claimed. Our arithmetic from (iii): since 7 ≡ 1 mod 6, the stated bound gives lim sup ≥ 1.57^(−7) ≈ 0.0425 for k=7.
  - (b) No octagon statement and no bipartite D=8 statement. Note that the authors call the polarity route available only for n admitting a polarity, which excludes octagons.

## 2. Miller & Širáň, "Moore graphs and beyond: A survey of the degree/diameter problem", Electron. J. Combin., Dynamic Survey DS14, revision 2 (2013)

- URL: https://www.combinatorics.org/files/Surveys/ds14/ds14v2-2013.pdf (DOI per Semantic Scholar: 10.37236/35). Local copy: `dl/ms_survey_ds14v2_2013.pdf`.
- Section 3.3.1, p. 19 (general graphs). Quotes:
  - "For larger diameter, it seems more reasonable to focus on asymptotic behaviour of n∆,D for fixed D while ∆ → ∞. Delorme [119] introduced the parameter µD = lim inf ∆→∞ n∆,D/∆^D."
  - "Trivially, µD ⩽ 1 for all D, and µ1 = 1; the bound (6) shows that µ2 = 1 as well. Further results of Delorme [118] imply that µD is equal to 1 also for D = 3 and D = 5."
  - "The values of µD for other diameters D are unknown. For example, for diameter 4 we only know that µ4 ⩾ 1/4; see Delorme [120] for more information."
- Section 3.4.5, p. 36 (bipartite). Quote: "In the same papers, Delorme also studied the asymptotic behaviour of the problem by introducing the parameter β_D = lim inf ... we see that β_D ⩽ 1 for all D; so far, it is only known [118, 119] that equality holds for D = 2, 3, 4 and 6."
- References: [118] C. Delorme, "Grands graphes de degré et diamètre donnés", European J. Combin. 6 (1985) 291–302. [119] C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 8 (1985) 325–334. [120] C. Delorme, "Examples of products giving large graphs with given degree and diameter", Discrete Appl. Math. 37/38 (1992) 157–167.
- Answers:
  - (a) Liminf-based: µ_D = 1 is known for D = 1, 2, 3, 5. D=4 has µ_4 ≥ 1/4. "The values of µD for other diameters D are unknown," so D=7 is not known as of 2013. The survey uses liminf only, so a sparse family could not decide µ_7 even if it gave limsup 1.
  - (b) Bipartite: β_D = 1 is known only for D = 2, 3, 4, 6. D=8 is not listed.
  - Attribution: the survey gives the EJC paper [118] as the source of µ_3 = µ_5 = 1. Bachratý et al. (section 1) give the JGT paper [6] as the source of the same statement. The two attributions conflict; the EJC text would settle it.

## 3. Delorme, "Grands graphes de degré et diamètre donnés", European J. Combin. 6 (1985) 291–302 (doi:10.1016/S0195-6698(85)80043-3). FULL TEXT NOT READ

- Record (Semantic Scholar API, https://api.semanticscholar.org/graph/v1/paper/DOI:10.1016/S0195-6698(85)80043-3?fields=title,abstract,year,citations.title,citations.year): title "Grands Graphes de Degré et Diamètre Donnés", year 1985, venue "European journal of combinatorics (Print)", author C. Delorme, DBLP key journals/ejc/Delorme85, citationCount 42, abstract null (elided by publisher).
- Access attempts: https://www.sciencedirect.com/science/article/pii/S0195669885800433 gave a Cloudflare error page ("There was a problem providing the content you requested", reference a4fade61298dd471). The PDF link (…/S0195669885800433/pdf) gave HTTP 403. Not bypassed. The DBLP record page returned a bot challenge (not bypassed).
- Secondary evidence on its contents:
  - Survey [118] is credited with µ_3 = µ_5 = 1 (liminf); see section 2.
  - Comellas 2024/2026 table, Table 2 (p. 5): "B′ Quotient of the bipartite graph B by a polarity [14]", where [14] = this EJC paper (section 4).
- Not verified: whether D=7, octagons, or any limsup statement appear in it. Next step: get the PDF through institutional access and grep for "octogone", "octagon", "7", "limsup".

## 4. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9(3) (1985) 325–334

- Identifiers: zbMATH Open id 4010570 (Zbl 0623.05048); DOI 10.1002/jgt.3190090304 (https://doi.org/10.1002/jgt.3190090304); DBLP journals/jgt/Delorme85; Semantic Scholar citationCount 74.
- Volume: zbMATH and the DOI say 9. The 2013 survey and Bachratý et al. say 8. Treat 9 as the likely correct volume.
- Wiley page (https://onlinelibrary.wiley.com/doi/10.1002/jgt.3190090304) returned a bot challenge. Not bypassed. Abstract not retrieved.
- Table notation (Comellas, arXiv:2406.18994, Table 2): "⊗B The component with polarity of the cartesian product of a bipartite graph B by itself [15]", where [15] = this JGT paper. (Text as printed; the operation as described is the tensor/Kronecker product, see section 5.)
- Answers: this is the source the survey and Bachratý et al. credit for µ_D/lim sup = 1 for k in {2,3,5} and for β_D=1 for bipartite D in {2,3,4,6}. Its statement about octagons is unknown.

## 5. Comellas, "Table of large graphs with given degree and diameter", arXiv:2406.18994 (PDF labelled "Table 1: Largest (∆,D)-graphs (January 2026)")

- URL: https://arxiv.org/abs/2406.18994 (local copy: `dl/arxiv_2406_18994.pdf`).
- Table 2 (p. 5), quotes: "B′ Quotient of the bipartite graph B by a polarity [14]"; "⊗B The component with polarity of the cartesian product of a bipartite graph B by itself [15]".
- Acknowledgements (p. 5): "We would like to acknowledge the invaluable contributions of Charles Delorme, who sadly passed away in 2015. The format of this table and detailed information on the graphs and graphs operations are based on his work."
- Table 1, row Δ=15: value 1215 at D=3 with code "(⊗Q2,4)′" (reading of the column alignment). 1215 = 27 × 45, which matches the point and line counts of GQ(2,4). So Q_{2,4} is presumably the GQ(2,4) incidence graph. This is our reading, not stated in the source.
- Table 1, row Δ=15, D=7: value 8,599,986, code "Loz". No octagon code appears anywhere in Table 1 or Table 2.
- The PDF I downloaded contains no asymptotic (lim sup / lim inf) statements. The 2026 citations to the Cames van Batenburg–Korsky preprint are not used here.

## 6. Other records checked

- Delorme, "Examples of products giving large graphs with given degree and diameter", Discrete Appl. Math. 37/38 (1992) 157–167, doi:10.1016/0166-218X(92)90130-3. IAOR record (https://iaorifors.com/paper/8475, Article ID iaor1993627) quotes: "The paper gives some constructions giving large graphs with given degree and diameter," and "and for some diameters the asymptotic growth is improved." Full text not read. ScienceDirect pii 0166218X92901303 not retrieved. Survey [120] is the source of µ_4 ≥ 1/4.
- Delorme, "Grands graphes de degré et diamètre fixés", Ann. Discrete Math. 17 (1983) 65–73 (Marseille-Luminy proceedings, Combinatorial Mathematics), zbMATH Zbl 0527.05041 (zbMATH id 3836079). Keywords: maximum number of vertices; simple undirected graph; maximum degree; diameter; constructions. Possibly the "III" paper in the brief. The brief's "Annals 13 (1982)" is NOT confirmed. No abstract.
- Canale & Gómez, "Asymptotically large (Δ,D)-graphs", Discrete Appl. Math. (2005), doi:10.1016/j.dam.2005.03.008 (Semantic Scholar DBLP journals/dam/CanaleG05; no abstract). Content NOT accessed. Candidate for general-D asymptotics, so a lead.

## 7. Our own check on the octagon route (not literature; hand derivation, not computer-verified)

- Setup: G is the incidence graph of a generalized octagon of order (s,t), with points P and lines L. Let Q have vertex set P×L, with (p,l) ~ (p',l') iff p ~ l' and l ~ p' in G. Q is the polarity quotient of the component (P×L) ∪ (L×P) of G×G. The swap σ(x,y)=(y,x) is fixed-point-free on that component.
- Claimed properties, derived by hand:
  - Order |P||L|.
  - Degree deg(p)·deg(l) = (t+1)(s+1) for every pair (loops at incident pairs removed).
  - Diameter ≤ 7, because the distance between [(p,l)] and [(p',l')] is at most min(max(d(p,p'), d(l,l')), max(d(p,l'), d(l,p'))), and point–line distances in the octagon incidence graph are at most 7.
  - The tensor component (P×L)∪(L×P) is regular of degree (t+1)(s+1), bipartite, diameter ≤ 8, with 2|P||L| vertices.
- With s=q, t=q² (q=2^(2e+1)): |P| = (1+q)(1+q³)(1+q⁶), |L| = (1+q²)(1+q³)(1+q⁶). For q=2 these give 1755 and 2925, matching the brief. Δ = (1+q)(1+q²). Then |P||L|/Δ^7 → 1 as q→∞, so lim sup n(Δ,7)/Δ^7 = 1 along Δ_q. The bipartite analogue 2|P||L| versus M_b(Δ,8) ≈ 2Δ^7 gives lim sup n_b(Δ,8)/M_b(Δ,8) = 1 along the same sequence.
- Sanity checks:
  - Same construction on GQ(2,4): 27 × 45 = 1215 at Δ=15, D=3. This equals the table entry (15,3)=1215, so the table's "(⊗Q2,4)′" is this construction.
  - Octagon analogue at Δ=15: 1755 × 2925 = 5,133,375 at D=7. This is below the table's (15,7) = 8,599,986, so it would not be a record. Its absence from the table does not show it is unknown.
- Key open question: does the JGT ⊗ construction plus the EJC quotient come with a general theorem "diam(B′) = diam(B) − 1 for any bipartite B"? If so, Delorme's 1985 framework already implies the octagon case, but no accessed source says so.

## 8. Discrepancies and cautions

- JGT volume 8 (survey, Bachratý et al.) versus 9 (zbMATH, DOI, Comellas).
- Attribution of µ_3 = µ_5 = 1: EJC [118] (survey) versus JGT [6] (Bachratý et al.).
- The brief's "Large graphs with given degree and diameter III, Annals of Discrete Math 13 (1982)" is not confirmed. zbMATH has a Delorme paper in Ann. Discrete Math. 17 (1983).
- The 2024 table PDF's Table 1 label says "January 2026"; the arXiv record shows it was updated after the 2024 submission.

## 9. Next leads

1. Get the full text of EJC 1985 (doi:10.1016/S0195-6698(85)80043-3) and JGT 1985 (doi:10.1002/jgt.3190090304) through institutional access. Grep for octagon, octogone, ⊗, "generalized 8-gon", and any limsup statement.
2. Read Delorme–Gómez, "Some new large compound graphs", EJC 23 (2002), doi:10.1006/eujc.2002.0581, and the 2020 JCTB paper "Approximate Moore graphs are good expanders" (doi:10.1016/j.jctb.2019.08.003). Both are citing papers in the Semantic Scholar list and may summarise the asymptotic status.
3. Computer check of the quotient lemma on small cases: GQ(2,2) → expect diameter 3; GQ(2,4) → expect degree 15 and diameter 3; GH(2,2) (incidence graph diameter 6) → expect diameter 5. Then GO(2,4) (incidence graph 1755 + 2925 vertices, point degree 5, line degree 3) → expect diameter 7 for the quotient (order 5,133,375; all-pairs BFS too big, so sample eccentricities).
4. Canale & Gómez, DAM 2005: obtain the abstract (Elsevier/Crossref) to see whether it treats general D.

## 10. Sources accessed

- https://arxiv.org/abs/1709.09760 and https://arxiv.org/pdf/1709.09760 (accessed, full text)
- https://www.combinatorics.org/files/Surveys/ds14/ds14v2-2013.pdf (accessed, full text)
- https://arxiv.org/pdf/2406.18994 (accessed, full text; Table 1 and Table 2)
- https://api.semanticscholar.org/graph/v1/paper/DOI:10.1016/S0195-6698(85)80043-3 and /citations (accessed, JSON)
- https://api.semanticscholar.org/graph/v1/paper/DOI:10.1002/jgt.3190090304 (accessed, JSON)
- https://api.semanticscholar.org/graph/v1/paper/DOI:10.1016/0166-218X(92)90130-3 (accessed, JSON)
- https://api.zbmath.org/v1/document/_search (accessed, JSON; ids 3809492, 3836079, 4010570)
- https://iaorifors.com/paper/8475 (accessed; abstract fragments)
- https://en.wikipedia.org/wiki/Degree_diameter_problem (accessed; no Delorme-specific statement)
- BLOCKED (no bypass): ScienceDirect EJC 1985 (Cloudflare error, a4fade61298dd471), Wiley JGT 1985 (bot challenge), DBLP record page (bot challenge)
