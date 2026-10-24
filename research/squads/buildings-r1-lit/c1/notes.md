# Card c1: Delorme, "Large bipartite graphs with given degree and diameter"

Scope: what C. Delorme, J. Graph Theory 9(3) (1985) 325-334, doi:10.1002/jgt.3190090304, proves, per questions (a)-(c) of the brief.

Access status: the full text was NOT obtained. https://onlinelibrary.wiley.com/doi/10.1002/jgt.3190090304 returned HTTP 403 to WebFetch. The publisher abstract was retrieved from Crossref and OpenAlex (identical text). Everything about the construction comes from later sources that describe the paper. Anything not backed by a quoted source is marked "unverified".

Local copies (in dl/): crossref_delorme.json, openalex_delorme.json, zb_search.json, ds14v2-2013.pdf, ds14.txt, comellas_2406.18994.pdf, comellas.txt, isham_2608.27253.pdf (pointer only).

---

## Short answers

- (a) Bipartite: the paper's own abstract gives only a positive constant, lim inf_{Delta->inf} B Delta^{1-D} = b_D > 0, for every D >= 2. It does not claim ratio 1 for any bipartite D. The survey (DS14, 2013) reads the bipartite result as equality (ratio 1, via lim inf) only for D = 2, 3, 4, 6. No source found gives bipartite ratio 1 for D outside {2,3,4,6}. Ratio 1 for ORDINARY graphs is claimed for D = 3 and D = 5.
- (b) Kronecker with Opp(G): attributed to this paper by two sources (Comellas Table 2 notation; a known preprint, pointer only). The survey describes the bipartite constructions as "bipartite versions of ... *-product and compounding" and does not name Kronecker. Octagons: no source found. D = 8: not discussed (bipartite Moore graphs exist only for D = 2, 3, 4, 6).
- (c) Families: the only explicit families I could verify are ordinary-graph quotients (Comellas Table 1 check below). The bipartite family is my derivation, unverified. Explicit bipartite values for D = 5 come from Bond-Delorme 1988, not from this paper.

---

## Finding 1 (answers a): the abstract

Reference: C. Delorme, "Large bipartite graphs with given degree and diameter", J. Graph Theory 9(3) (1985) 325-334. Abstract via Crossref https://api.crossref.org/works/10.1002/jgt.3190090304 and OpenAlex https://api.openalex.org/works/doi:10.1002%2FJGT.3190090304 (both agree). zbMATH review, Zbl 0623.05048: https://zbmath.org/4010570 (same text, reviewer field empty). Page: abstract, p. 325.

Quote (Crossref text with JATS tags removed; the stray period after B is in the source):
"We give constructions of bipartite graphs with maximum Delta, diameter D on B vertices, such that for every D >= 2 the lim inf_{Delta->inf} B. Delta^{1-D} = b_D > 0. We also improve similar results on ordinary graphs, for example, we prove that lim_{Delta->inf} N . Delta^{-D} = 1 if D is 3 or 5. This is a partial answer to a problem of Bollobas."

Answers (a): For bipartite graphs, only a positive constant b_D for every D >= 2. Since the bipartite Moore bound is about 2 Delta^{D-1}, this is a constant-factor bound, not ratio 1. The value of b_D is not stated in the abstract (unverified). Ratio 1 (lim N Delta^{-D} = 1) is stated only for ORDINARY graphs and only for D = 3 and 5.

---

## Finding 2 (answers a): which bipartite D reach ratio 1 (survey)

Reference: M. Miller and J. Siran, "Moore graphs and beyond: A survey of the degree/diameter problem", Electron. J. Combin., Dynamic Survey DS14, v2 (2013), doi:10.37236/35. PDF: https://www.combinatorics.org/files/Surveys/ds14/ds14v2-2013.pdf (92 pages; saved as dl/ds14v2-2013.pdf). Section 3.4.5, printed p. 36.

Quote: "In the same papers, Delorme also studied the asymptotic behaviour of the problem by introducing the parameter [beta_D = lim inf_{Delta->inf} b_{Delta,D} / (2 Delta^{D-1}), formula as typeset] where b_{Delta,D} is the largest order of a bipartite (Delta,D)-graph. Comparing this with the bipartite Moore bound, we see that beta_D <= 1 for all D; so far, it is only known [118, 119] that equality holds for D = 2, 3, 4 and 6."

Notes: [118] = Delorme, EJC 6 (1985) 291-302; [119] = this paper. The survey's reference list gives this paper as "J. Graph Theory 8 (1985)". Crossref and Wiley give volume 9, so the survey has a typo. beta_D uses lim inf. If beta_D = b_D/2 (my inference from the two definitions), the survey and the abstract agree.

Answers (a): the survey reads the 1985 bipartite results as proving equality only for D = 2, 3, 4, 6. No bipartite D outside {2,3,4,6} is listed with ratio 1.

Also in the same section (quote): "Other constructions of large bipartite graphs were found by Delorme [118, 119], using bipartite versions of operations described earlier, most notably, *-product and compounding." (Answers b: the survey names the star product and compounding, not Kronecker or Opp.)

Related exact statements from the same survey (for (c) context):
- Section 3.4.4, p. 33-34: "They proved that such graphs exist only if the diameter is 2, 3, 4 or 6." (Feit-Higman and Singleton, bipartite Moore graphs.) Also: "For D = 3, 4, 6 bipartite Moore graphs of degree Delta have been constructed only when Delta - 1 is a prime power [41]."
- Section 3.4.4, p. 36: "Additionally, we know that b3,5 = B3,5 - 6 and b7,3 = B7,3 - 6. The value of b3,5 corresponds to an optimal bipartite graph of degree 3, diameter 5 and order 56 found by Bond and Delorme [64], whose optimality was proved by Jorgensen [216]."

---

## Finding 3 (answers a, b): ordinary-graph statements attributed to Delorme

Reference: same survey, section 3.3.1, printed p. 19.

Quotes:
"Delorme [119] introduced the parameter mu_D = lim inf_{Delta->inf} n_{Delta,D} / Delta^D."
"Further results of Delorme [118] imply that mu_D is equal to 1 also for D = 3 and D = 5."
"For example, for diameter 4 we only know that mu_4 >= 1/4; see Delorme [120] for more information."

Notes: the survey credits the mu = 1 result for D = 3, 5 to [118] (EJC 1985), while the abstract (Finding 1) claims it in this paper. Ordinary graphs only, so this is not a bipartite result and does not meet score 3.

---

## Finding 4 (answers b, c): the Kronecker-with-polarity operation is credited to this paper (ordinary-graph table)

Reference: F. Comellas, "Table of large graphs with given degree and diameter", arXiv:2406.18994v2 (24 Jan 2026), https://arxiv.org/abs/2406.18994 (PDF saved as dl/comellas_2406.18994.pdf). Table 2 (operations), p. 5.

Quotes:
"⊗B The component with polarity of the cartesian product of a bipartite graph B by itself [15]"
"B' Quotient of the bipartite graph B by a polarity [14]"
"Hq Incidence graph of a regular generalized hexagon [3]" and "Qq Incidence graph of a regular generalized quadrangle [3]"
References: [14] = C. Delorme, Grands graphes de degre et diametre donnes, Europ. J. Combin. 6 (1985) 291-302. [15] = C. Delorme, Large bipartite graphs with given degree and diameter, J. Graph Theory 9 (1985) 325-334.

Notes: the text says "cartesian product", but the symbol and the "component with polarity" description match a Kronecker (tensor) self-product. This reading is mine. The table lists ORDINARY (Delta,D)-graphs, not bipartite ones.

Cross-check (my arithmetic on Comellas Table 1, row Delta = 16, names above the row): D = 3 entry is 1600 with label (⊗Q3)', and D = 5 entry is 132 496 with label (⊗H3)'. Check: 1600 = 40^2, where 40 = (1+3)(1+3.3) is the point count of GQ(3,3). 132 496 = 364^2, where 364 = (1+3)(1+3.3+3^2.3^2) is the point count of GH(3,3). So the ordinary quotient has order |A||B| for base B = incidence graph of GQ or GH, with degree (q+1)^2 = 16. This fits the construction described in the brief.

---

## Finding 5 (answers b): attribution pointer, already-known source (NOT counted, NOT new)

arXiv:2608.27253 (Isham, Lakhotia, Monroe, Petrini), section 3.4.2 and reference list, cites this paper as [20]. Quote from section 3.4.2: "Delorme constructed another family of diameter-3 graphs approaching the Moore bound in [20], based on the polarity quotient (with any self-loops removed) of the Reduced-Kronecker product of a large bipartite graph G(U = (A, B), E) and its opposite Opp(G) = G(U = (B, A), E)..."

Note: this attribution is for the ORDINARY polarity quotient (diameter 3). The same section gives order (1+s)(1+t)(1+st)^2 and degree (1+s)(1+t) for GQ(s,t). With s = t = 3 this is order 1600 at degree 16, which matches the Comellas entry in Finding 4.

---

## Finding 6 (answers c): explicit bipartite values from the same author's work (NOT this paper)

Reference: J. Bond and C. Delorme, "New large bipartite graphs with given degree and diameter", Ars Combin. 25C (1988) 123-132, Zbl 0649.05043, https://zbmath.org/4059445 (reviewer: J. Plesnik).

Quote (zbMATH review, LaTeX normalized): "The double cover construction of N. Biggs ... is used to produce large bipartite graphs of given maximal degree Delta and diameter D. E.g. for Delta = 3 and D = 5 a graph with 56 vertices is given. A table is presented of best known orders if 3 <= Delta <= 16 and 3 <= D <= 10 with the corresponding references."

Also DS14 Table 4 (CombinatoricsWiki bipartite table, accessed 10 March 2013; printed p. 37): rows Delta = 3: D = 3..10 give 14, 30, 56, 126, 168, 256, 506, 800. Delta = 4: 26, 80, 160, 728, 840, 2 184, 4 970, 11 748.

---

## Finding 7 (answers b): octagons and D = 8

- Survey DS14 and Comellas arXiv:2406.18994: the string "octagon" occurs 0 times in both texts (grep, dl/ds14.txt and dl/comellas.txt).
- WebSearch on "generalized octagon Ree-Tits ... Delorme" returned only generic octagon references (FinInG arXiv:1606.05530; Coolsaet; Ihringer-Sin-Xiang). None links octagons to degree-diameter work.
- Verdict: no evidence that the 1985 paper uses generalized octagons or D = 8. Unverified in the full text.

---

## Finding 8 (other Delorme papers to check next)

- C. Delorme, "Grands graphes de degre et diametre donnes", Europ. J. Combin. 6 (1985) 291-302 [DS14 ref 118; Comellas ref 14]. Survey credits it with mu_3 = mu_5 = 1 and with bipartite equality for D = 2, 3, 4, 6. Full text not accessed.
- C. Delorme, "Examples of products giving large graphs with given degree and diameter", Discrete Appl. Math. 37/38 (1992) 157-167, doi:10.1016/0166-218X(92)90130-3 [DS14 ref 120]. No abstract available (Crossref and Semantic Scholar both empty). Survey cites it for mu_4 >= 1/4.
- C. Delorme and J. Gomez, "Some new large compound graphs", Europ. J. Combin. 23(5) (2002) 539-547, doi:10.1006/eujc.2002.0581. Crossref metadata only, no abstract.
- E. Canale and J. Gomez, "Asymptotically large (Delta,D)-graphs", Discrete Appl. Math. 152 (2005) 89-108, doi:10.1016/j.dam.2005.03.008. Crossref metadata only, abstract not retrieved (Crossref and Semantic Scholar null). Content unverified. This is the brief's "Canale-Gomez 2005" candidate.
- C. Delorme, L.K. Jorgensen, M. Miller, G. Pineda-Villavicencio, "On bipartite graphs of diameter 3 and defect 2", J. Graph Theory 61(4) (2009) 271-288, doi:10.1002/jgt.20378. Defect results, not asymptotics. The survey (p. 34) says defect-2 bipartite graphs can exist only for diameter 3.

---

## Unverified (could not check from this sandbox)

- The value of b_D and the exact theorem statements of the 1985 paper.
- Whether the bipartite component of the Kronecker self-product (or of B with Opp(B)) has the same diameter as B, as the brief says.
- Whether octagons or D = 8 appear.
- The exact bipartite families (Delta, D, order). My derivation, unverified against the paper: for base B = incidence graph of a generalized quadrangle GQ(q,q), a bipartite component of B x Opp(B) would have degree (q+1)^2 and order 2((q+1)(q^2+1))^2 (diameter 4 if the diameter is preserved). Analogous formulas for GH(q,q) (D = 6) and PG(2,q) (D = 3) give ratio 1 asymptotically, consistent with the survey's "equality for D = 2, 3, 4, 6".

---

## Bottom line for the squad

- Score rule 3 (bipartite ratio 1 for D outside {2,3,4,6}): NOT met. No source found, including the abstract.
- Score rule 2 (Kronecker/Opp or octagon construction used for bipartite degree-diameter with explicit asymptotics): NOT met strictly. The Kronecker link comes from Comellas (ordinary table) and from a known preprint (pointer only). The survey gives the explicit bipartite asymptotic but names star product and compounding.
- Score rule 1 (exact statement of which D are known): MET. Survey 2013: bipartite equality known only for D = 2, 3, 4, 6, credited to Delorme [118, 119].
