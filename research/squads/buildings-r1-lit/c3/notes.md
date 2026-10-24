# c3 notes: asymptotics in Miller and Širáň, DS14 (degree/diameter survey)

## 0. Source and version check

- Downloaded from https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS14/pdf/ (HTTP 200, application/pdf, 901,591 bytes, 92 pages, sha256 149fba3ac4eaef086a1f9fe92967d4f5abe619c6e7f3aca0e7249c34f6df7c08). The same sha256 as https://www.combinatorics.org/files/Surveys/ds14/ds14v2-2013.pdf.
- Local copies: research/squads/buildings-r1-lit/c3/dl/ds14_survey.pdf; per-page text with [pdfN] tags in dl/ds14_paged.txt; page images pg18, pg19, pg27, pg36, pg37 (PNG) used to check formulas. Printed page number equals PDF page index (checked on pp. 18, 36, 37).
- The survey is "Moore graphs and beyond: A survey of the degree/diameter problem", M. Miller and J. Širáň, Electron. J. Combin. Dynamic Survey DS14, #DS14v2 (20(2), 2013). The EJC landing page (https://www.combinatorics.org/ojs/index.php/eljc/article/view/DS14, also https://www.combinatorics.org/ds14) gives "This Version: DS14: May 16, 2013", first published 2005. It lists no later version.
- WebSearch for a third edition or DS14v3 found nothing. No DS14 revision dated 2020-2026 exists in what I could reach. The OU repository record https://oro.open.ac.uk/41753 returned HTTP 403 and was not read.
- Other later survey found: P. Steller, MSc thesis, University of Delaware, 2020, "A survey of the degree/diameter problem for undirected graphs". Landing page https://udspace.udel.edu/handle/19716/28430, PDF https://udspace.udel.edu/bitstreams/45f012e8-720c-47be-9507-63aacc42aa87/download, local copy dl/steller2020_thesis.pdf. It has no asymptotic statements (no lim, no "→ ∞", no "sufficiently large" results). Its bipartite material is Moore bipartite graphs and defect 2. Example, thesis pdf p.49: "For k ≥ 3 and d ≥ 3, Moore bipartite graphs only exist for d = 3, 4, or 6 [28]."
- Quote convention: quotes marked (img) were read from rendered page images (pp. 18, 19, 27, 36, 37). All other quotes come from the PDF text layer. Typesetting problems in the text layer are listed in section 8.

## 1. Part (a): general graphs, n(Δ,D) and its limits

**A1. µ_D definition** (p.19, §3.3.1 General overview). Quote: "For larger diameter, it seems more reasonable to focus on asymptotic behaviour of n∆,D for fixed D while ∆ → ∞. Delorme [119] introduced the parameter µD = lim inf ∆→∞ n∆,D / ∆^D." (img)
- Refs: [119] C. Delorme, Large bipartite graphs with given degree and diameter, J. Graph Theory 8 (1985) 325–334. The general-graph parameter is introduced in a bipartite paper.

**A2. Values of µ_D** (p.19). Quote: "Trivially, µD ⩽ 1 for all D, and µ1 = 1; the bound (6) shows that µ2 = 1 as well. Further results of Delorme [118] imply that µD is equal to 1 also for D = 3 and D = 5." (img)
- Refs: [118] C. Delorme, Grands graphes de degré et diamètre donnés, European J. Combin. 6 (1985) 291–302. The "(6)" is the Brown-graph bound in A5, citing [318] and [20].

**A3. Other D** (p.19). Quote: "The values of µD for other diameters D are unknown. For example, for diameter 4 we only know that µ4 ⩾ 1/4; see Delorme [120] for more information." (img)
- Refs: [120] C. Delorme, Examples of products giving large graphs with given degree and diameter, Discrete Appl. Math. 37/38 (1992) 157–167.
- Summary: µ_D = 1 for D ∈ {1,2,3,5}, µ_4 ⩾ 1/4, and no value for D ≥ 6 or for D = 4 beyond that. The survey never uses lim sup.

**A4. Bollobás conjecture** (p.19). Quote: "...the conjecture of Bollobás [62] that, for each ε > 0, it should be the case that n∆,D > (1 − ε)∆^D if ∆ and D are sufficiently large." (img)
- Refs: [62] B. Bollobás, Extremal Graph Theory, Academic Press, 1978. Restated as open problem 7 (p.70). The 2026 preprints named by the coordinator are not re-reported here.

**A5. Lower bounds for D = 2** (p.18 eqs. (4), (5); p.19 eq. (6)).
- Eq. (4): n∆,2 ⩾ ∆² − ∆ + 1 whenever ∆ − 1 is a prime power (Brown graph). Ref [76] W.G. Brown, On graphs that do not contain a Thompsen graph, Canad. Math. Bull. 9 (1966) 281–285.
- Eq. (5): n∆,2 ⩾ ∆² − ∆ + 2 if ∆ − 1 is a power of 2. Refs [135] P. Erdős, S. Fajtlowicz, A.J. Hoffman, Networks 10 (1980) 87–90, and Delorme [120].
- Eq. (6), quote: "Using this fact, it was shown in [318] that Brown graphs can be modified to give, for all sufficiently large ∆, the inequality n∆,2 ⩾ ∆² − 2∆^1.525" (img). Uses the prime-gap result of [20] R.C. Baker, G. Harman, J. Pintz, The difference between consecutive primes II, Proc. London Math. Soc. (3) 83 (2001) 532–562. [318] J. Širáň, J. Šiagiová, M. Ždímalová, Large graphs of diameter two, preprint.
- This is the source of µ_2 = 1 in A2.

**A6. Canale–Gómez bound, all D ⩾ 3** (p.18, §3.3.1). Quote: "A substantial progress was achieved by Canale and Gómez [84] by exhibiting, for an infinite set of values of ∆, families of graphs showing that n∆,D ⩾ (∆/1.6)^D for all D ⩾ 3; the constant in the denominator can be replaced by 1.57 for D congruent with −1, 0, or 1 (mod 6)." (img)
- Refs: [84] E.A. Canale, J. Gómez, Asymptotically large (∆,D)-graphs, Discrete Appl. Math. 152 (2005) 89–108.
- Note: only for an infinite set of ∆, so this is not a bound for all ∆. It gives ratio at least 1.6^(−D) to Δ^D.

**A7. de Bruijn and Kautz** (p.17, §3.3.1). Quote: "These graphs therefore give, for any ∆ and D, the lower bound n∆,D ⩾ (∆/2)^D." (text layer; no reference number in the text for the undirected de Bruijn graph). Also quote: "Thus, for any D and even ∆, such graphs improve the bound given de Bruijn graphs, and consequently, we have N∆,D ⩾ (∆/2)^D + (∆/2)^(D−1)" (text layer; Kautz construction).
- Refs: Kautz [222] W.H. Kautz, Bounds on directed (d,k) graphs, AFCRL-68-0668 (1968). Baskoro–Miller [32] E.T. Baskoro, M. Miller, On the construction of networks with minimum diameter, Australian Computer Science Communications 15 (1993) 739–743. The survey says the Baskoro–Miller construction, ignoring directions, gives "the same" order for even ∆ (p.17–18).

**A8. Imase–Itoh and the older families** (p.18). Quote: "An adaptation of the digraph construction of Imase and Itoh [208] also gives (∆, D)-graphs of order at least ⌈∆/2⌉^D." Quote: "all giving (∆, D)-graphs of order f(∆)(∆ − 1)^⌈D/2⌉ + g(∆), where f and g depend on ∆ but not on D." (img)
- Refs: [208] M. Imase, M. Itoh, IEEE Trans. Computers C-30 (1981) 439–442. [134] B. Elspas (1964). [168] H. Friedman, IEEE Trans. EC-15 (1966) 253–254 (printed as 1996 in the bibliography). [228] I. Korn, IEEE Trans. EC-16 (1967) 90. [5] S.B. Akers, IEEE Trans. EC-14 (1965) 448. [13] B.W. Arden, H. Lee, IEEE Trans. Comput. 30 (1981) 291–295.
- My reading, not the survey's words: the exponent ⌈D/2⌉ is smaller than D for D ⩾ 2, so these constructions give nothing at scale Δ^D.

**A9. Bermond–Bollobás question** (p.16, end of §3.2). Quote: "Is it true that for each positive integer c there exist ∆ and D such that the order of the largest graph of maximum degree ∆ and diameter D is at most M∆,D − c?" (text layer)
- Refs: [43] J.-C. Bermond, B. Bollobás, The diameter of graphs: a survey, Congressus Numerantium 32 (1981) 3–27. Open problem 6 (p.70).

**A10. Vertex-transitive and Cayley: positive-density Moore gaps** (p.25 §3.4.1; p.27 §3.4.2). Quote (p.25): "for any fixed ∆ ⩾ 3 and c ⩾ 2 there exists a set S of natural numbers of positive density such that vt∆,D ⩽ M∆,D − c, for all D ∈ S." (text layer)
- Quote (p.27, Cayley): "For the remaining pairs (∆, D) with ∆ ⩾ 3 we currently do not have a better upper bound on C∆,D than M∆,D − 2."
- Refs: [213] R. Jajcay, M. Mačaj, J. Širáň, The vertex-transitive Moore bound, in preparation.

**A11. vt, diameter 2** (p.26 §3.4.1). Text layer: "vt∆,2 ⩾ 2q² for all odd ∆ ⩾ 5, where q is the largest prime power such that q ≡ 5 mod 8 and (∆ + 1)/2 < q < (2∆ + 1)/3." (The subscript 2 is missing in the text layer and is inferred.)
- Refs: [249] B.D. McKay, M. Miller, J. Širáň, J. Combin. Theory Ser. B 74 (1998) 110–118; [318] as in A5.

**A12. vt, Faber–Moore–Chen type, fixed D** (p.26). Text layer: "vt∆,D ⩾ ((∆ + 3)/2)! / ((∆ + 3)/2 − D)! for all pairs (∆, D) in the range 3 ⩽ D ⩽ 0.3∆."
- Refs: [245] H. Macbeth, J. Šiagiová, J. Širáň, T. Vetrík, Large Cayley graphs and vertex-transitive non-Cayley graphs of given degree and diameter, J. Graph Theory 64 (2010) 87–98; underlying digraphs [144] V. Faber, J.W. Moore, W.Y.C. Chen, Networks 23 (1993) 641–649; [178] J. Gómez, Networks 50 (2007) 241–250 (a non-asymptotic improvement, per the survey).
- My arithmetic: for fixed D, the ratio to Δ^D tends to 2^(−D).

**A13. Lifts of a dipole, diameter 2** (p.26). Text layer: "the maximum order of a lift of diameter 2 is, for sufficiently large ∆, bounded above by (4(10 + √2)/49)∆² ≃ .93∆²", compared with M∆,2 = ∆² + 1.
- Refs: [307] J. Šiagiová, Acta Math. Univ. Comenianae LXXI (2) (2002) 157–161.

**A14. Cayley graphs, diameter 2, along a sparse degree set** (p.27 §3.4.2, img). Quote: "one has C∆,2 > ∆² − 6√2 ∆^(3/2). This means that, at least for degrees ∆ ∈ 𝒟, the Moore bound M∆,2 can be approached asymptotically by Cayley graphs." Here 𝒟 = {2^(2m+µ) + (2+δ)2^(m+1) − 6, m ⩾ 1, µ ∈ {0,1}} (text layer).
- Refs: [312] J. Šiagiová, J. Širáň, Approaching the Moore bound for diameter two by Cayley graphs, J. Combin. Theory Ser. B 102 (2012) 470–473.

**A15. Cayley graphs, diameter 2, all large ∆** (p.27, img). Quote: "C∆,2 > (1/2)∆² − 1.39∆^1.525 for every sufficiently large ∆." This gives liminf C_{∆,2}/∆² ⩾ 1/2 along all large ∆.
- Refs: [318] as in A5; earlier result [311] J. Šiagiová, J. Širáň, A note on large Cayley graphs of diameter two and given degree, Discrete Math. 35 (2005) 379–382.

**A16. Cayley graphs, D ⩾ 3, general families** (p.27, img). Quote: "C∆,D ⩾ D((∆ − 3)/3)^D for ∆ ⩾ 5 and D ⩾ 3, and by Macbeth, Šiagiová and Širáň [244] who established the bound C∆,D ⩾ D((∆−2)/3)^D − D for ∆, D ⩾ 3 using just Cayley graphs of metacyclic groups."
- Refs: [245] as in A12; [244] H. Macbeth, J. Šiagiová, J. Širáň, Cayley graphs of given degree and diameter for cyclic, abelian, and metacyclic groups, Discrete Math. 312 (2012) 94–99.
- My arithmetic: the leading ratio to Δ^D is D/3^D.

**A17. Cayley graphs, D = 3, 4, 5** (p.27, img). Quote: "C∆,3 ⩾ (3/16)(∆ − 3)³, C∆,4 ⩾ 32((∆ − 8)/5)⁴ and C∆,5 ⩾ 25((∆ − 7)/4)⁵ for all ∆ ⩾ 10."
- Refs: [335] T. Vetrík, Cayley graphs of given degree and diameter 3, 4 and 5, Discrete Math., to appear.
- My arithmetic: the liminf of C/Δ^D is at least 3/16 for D = 3, 32/625 ≈ 0.0512 for D = 4, and 25/1024 ≈ 0.0244 for D = 5. Compare µ_3 = µ_5 = 1 for general graphs (A2).

**A18. Abelian Cayley, fixed d, D → ∞** (p.31, eq. (8), text layer). The inequality reads c·2^d/(d!·d·(ln d)^(1+log₂ e)) · D^d + O(D^(d−1)) ⩽ AC_{2d,D} ⩽ Σ_{i=0}^{d} 2^i C(d,i) C(D,i). Quote: "if the number of generators d is fixed and D → ∞ then the right hand side of (8) has the form 2^d D^d / d! + O(D^(d−1))." (text layer)
- The survey attributes the lower bound to Dougherty–Faber [132] (SIAM J. Discrete Math. 17 (2004) 478–519). The upper-bound attribution to Stanton–Cowan [326] (SIAM Review 12 (1970) 277–279) is inferred from the sentence on p.31.
- Exact values: AC_{4,D} = |W_{2,D}| = 2D² + 2D + 1 (Dougherty–Faber).

**A19. Abelian Cayley, D = 2** (p.32, text layer). Quote: "An unstated folklore conjecture asserts that one should have AC∆,2 ≈ ∆²/2 for all ∆; computational evidence due to McKay [248] has confirmed this for all ∆ ⩽ 16." Upper bound by counting: AC∆,2 ⩽ ∆²/2 + ∆ + 1.
- Current best: "AC∆,2 > (3/8)∆² − 1.45D^1.525 for all sufficiently large ∆" [318]. The text layer prints D where ∆ is expected, which I take to be a typo.
- Also [244]: AC∆,2 ⩾ (3/8)(∆² − 4) for ∆ = 4q − 2 (q odd prime power). AC∆,2 ⩾ (∆+1)²/3 for ∆ = 3q − 1.
- Refs: [248] B.D. McKay, personal communication (2006).

**A20. Abelian Cayley, D ⩾ 3 (text layer)**.
- Garcia–Peyrat [172] (Discrete Appl. Math. 75 (1997) 125–133), p.32: "for ∆ large enough and for 4 ⩽ D ⩽ ∆ they showed that AC∆,D ⩾ ∆^(D−2.17) / (21 D!)."
- Vetrík [336] (preprint), p.32: AC∆,3 ⩾ (9/128)(∆ + 3)²(∆ − 5) for ∆ = 8q − 3. Also AC∆,3 ⩾ (9/128)∆³ + O(D^2.525) for all sufficiently large ∆ (the error exponent is printed as D; I read it as ∆).

**A21. Circulant (cyclic) Cayley, D = 2** (p.32, text layer). Quote: "the expectation is that CC∆,D ≈ ∆²/2 for all sufficiently large ∆." Also CC∆,2 ⩾ ∆²/3 + O(∆^(3/2)) for ∆ = 3p + O(√p) [244], and CC∆,2 ⩾ (13/36)(∆+2)(∆−4) for ∆ = 6p−2 [336]. Quote: "No results for large Cayley graphs of cyclic groups for diameters larger than 2 have been known at the time of writing this survey."

**A22. Planar graphs, even D** (p.39, §3.4.6). Quote: "When the diameter is even, Tishchenko completely solved the degree/diameter problem for planar graphs, providing the exact value of p∆,D for large ∆." Text layer formula: p∆,2d = (3∆(∆ − 1)^d − 1) / (2(∆ − 2)).
- My arithmetic: this is about (3/2)∆^(D/2), so the exponent is D/2, not D.
- The survey gives no citation number at that sentence. Tishchenko's diameter-2 surface paper is [332] (p.38).

**A23. Surfaces, D = 2** (p.38, §3.4.6, text layer). Quote: "for diameter D = 2 and any maximum degree ∆ ⩾ ∆S, n∆,2(S) = n∆,2(S0) = ⌊(3/2)∆⌋ + 1." Quote: "The striking fact here is that this bound is, for ∆ ⩾ ∆S, independent of the surface S and is the same as for the plane!"
- Refs: [226] M. Knor, J. Širáň, Extremal graphs of diameter two and given maximum degree, embeddable in a fixed surface, J. Graph Theory 24 (1997) 1–8. The constant ∆_S is printed as "28(2 − χ(S))² + 2" (text layer; the exponent is uncertain).

**A24. Surfaces, general D** (p.39, text layer). Šiagiová–Simanjuntak [310] bound n∆,D(S) between ∆((∆−1)^⌊D/2⌋ − 2)/(∆ − 2) and c_{S,D} times the same expression, with c_{S,D} = (6D(ε+1) + 3). Quote: "In view of these bounds, the authors of [310] raise the natural question of the existence and the value of the limit of n∆,D(S)/∆^⌊D/2⌋ as ∆ → ∞." Refs: [310] J. Šiagiová, R. Simanjuntak, Acta Math. Univ. Comenianae LXXIII (2004) 115–118. Restated as open problem 14 (p.70).

**A25. Digraph aside, out of scope** (p.65). Quote: "Munoz and Gómez [273] continued this research and obtained new families of asymptotically optimal (d, k, k′, s)-digraphs." Ref [273] X. Munoz, J. Gómez, Asymptotically optimal (∆,D,s)-digraphs, Ars Combin. 49 (1998) 97–111. Also p.61, the abelian Cayley digraph bound with fixed d and k → ∞ (same shape as (8)).

## 2. Part (b): bipartite graphs

**B1. Bipartite Moore bound** (p.33, §3.4.4). Text layer: B_{2,D} = 2D and B_{∆,D} = 2((∆−1)^D − 1)/(∆−2) for ∆ > 2. Biggs [58] is cited (N.L. Biggs, Algebraic Graph Theory, 2nd ed., CUP 1993). My arithmetic: B_{∆,D} ~ 2∆^(D−1), the normalization the survey uses for β_D.

**B2. Which D admit bipartite Moore graphs** (p.33, text layer). Quote: "They proved that such graphs exist only if the diameter is 2, 3, 4 or 6." Refs: [148] W. Feit, G. Higman, The nonexistence of certain generalized polygons, J. Algebra 1 (1964) 114–131; [316] R.C. Singleton, J. Combin. Theory 1 (1966) 306–332.

**B3. Equality cases for Moore graphs** (p.33, text layer). Quote: "For D = 2 and each ∆ ⩾ 3 the bipartite Moore graphs of degree ∆ are the complete bipartite graphs of degree ∆. For D = 3, 4, 6 bipartite Moore graphs of degree ∆ have been constructed only when ∆ − 1 is a prime power [41]." Quote: "Singleton [316] proved that the existence of a bipartite Moore graph of diameter 3 is equivalent to the existence of a projective plane of order ∆ − 1." Ref [41] C.T. Benson, Minimal regular graphs of girth eight and twelve, Canad. J. Math. 18 (1966) 1091–1094.

**B4. Exact values b = B** (p.36, img). Quote: "considering bipartite Moore graphs for D = 2 and any ∆ ⩾ 2, we have b∆,2 = B∆,2. For D = 3, 4 and 6, whenever ∆ − 1 is a prime power, the value of b∆,D equals B∆,D. Additionally, we know that b3,5 = B3,5 − 6 and b7,3 = B7,3 − 6." Refs: b_{3,5} = 56 from [64] J. Bond, C. Delorme, New large bipartite graphs with given degree and diameter, Ars Combin. 25C (1988) 123–132, optimality [216] L.K. Jørgensen, Discrete Math. 114 (1993) 265–273. b_{7,3} = 80 from Hafner and Loz (no number given), optimality [152] R. Feria-Purón, M. Miller, G. Pineda-Villavicencio, Discrete Math. 313 (4) (2013) 381–390.

**B5. The bipartite asymptotic parameter β_D** (p.36, img). This is the main bipartite asymptotic statement. Quote: "In the same papers, Delorme also studied the asymptotic behaviour of the problem by introducing the parameter β_D = lim inf ∆→∞ b∆,D / (2∆^(D−1)), where b∆,D is the largest order of a bipartite (∆, D)-graph. Comparing this with the bipartite Moore bound, we see that β_D ⩽ 1 for all D; so far, it is only known [118, 119] that equality holds for D = 2, 3, 4 and 6."
- Refs: [118] C. Delorme, Grands graphes de degré et diamètre donnés, European J. Combin. 6 (1985) 291–302; [119] Delorme, Large bipartite graphs with given degree and diameter, J. Graph Theory 8 (1985) 325–334.
- Answer to the brief: lim inf (not lim sup) of b/(2∆^(D−1)) is 1 for D ∈ {2,3,4,6}, and the survey gives no value for any other D, including D = 5, 7, 8.

**B6. Defect results that restrict D** (p.34, text layer). "Thus, bipartite graphs of defect 2 can possibly exist only for diameter 3." Refs [124] Delorme, Jørgensen, Miller, Pineda-Villavicencio, J. Graph Theory 61 (4) (2009) 271–288; [125] same authors, European J. Combin. 30 (4) (2009) 798–808; [283] G. Pineda-Villavicencio, J. Algebraic Combin. 34 (2011) 163–182. "Thus, bipartite graphs of defect 4 exist only for diameters 3 and 4." Refs [154] R. Feria-Purón, G. Pineda-Villavicencio, Discrete Appl. Math. 160 (2012) 140–154; [152] as in B4.
- Large-D conjecture (p.34, text layer), stated in the survey as a conjecture from [283]: "For a given ∆0 and δ0 = f(∆0) there exists a constant D1 ⩾ D0 such that regular bipartite (∆0, D, −δ0)-graphs with D ⩾ D1 do not exist."

**B7. Delorme's bipartite constructions** (p.36, img). Quote: "Bond and Delorme [64, 65] gave new constructions of large bipartite graphs with given degree and diameter, using their concept of a partial Cayley graph. Other constructions of large bipartite graphs were found by Delorme [118, 119], using bipartite versions of operations described earlier, most notably, ∗-product and compounding." Ref [65] J. Bond, C. Delorme, A note on partial Cayley graphs, Discrete Math. 114 (1993) 63–74.
- No Kronecker product with an opposite graph appears anywhere in the survey. "opposite" occurs only as "oppositely directed darts" (p.21).

**B8. Table 4, largest known bipartite graphs** (p.37, img). Caption: "The order of the largest known bipartite graphs of maximum degree ∆ and diameter D, CombinatoricsWiki, accessed on 10 March 2013." Rows ∆ = 3..16, columns D = 3..10. This is a table of lower bounds, not an asymptotic statement. The D = 8 column (∆ = 3..16): 256, 2184, 9234, 29790, 80940, 201480, 449480, 1176480, 2246940, 4650100, 5314680, 14172480, 14172480, 36201060.
- My arithmetic on the D = 8 column, not from the survey: b/B_{∆,8} is 0.502 (∆=3), 0.333 (4), 0.211 (5), 0.153 (6), 0.105 (8), 0.109 (10), 0.109 (12), 0.099 (16). The ratio b/(2∆^7) lies between 0.048 and 0.067 for the eight ∆ values I checked (3, 4, 5, 6, 8, 10, 12, 16).
- The table also shows b = B for D = 3, 4, 6 whenever ∆−1 is a prime power, which matches B4.

**B9. Other bipartite constructions** (p.36, img). Quote: "Loz, Pérez-Rosés and Pineda-Villavicencio [240] adapted the voltage-assignment-based method developed by Loz and Širáň [242] for general graphs to the case of bipartite graphs; this resulted in updating more than one third of the table of the largest known bipartite graphs." Non-asymptotic.

## 3. Part (c): flags, buildings, Coxeter groups, generalized polygons (s,t)

- Nothing in the survey. I ran a case-insensitive whole-word search over the full text for: building(s), flag, Coxeter, Tits, Ree, Suzuki, unitary, Hermitian, octagon(s), hexagon(s), quadrangle(s), polygon(s), n-gon, Kronecker, tensor, opposite, incidence, and generalized. The only hits were:
  - "building-block network" (in the title of Imase–Itoh [208]);
  - "generalized Moore graphs" (p.16, p.65, p.77 bibliography);
  - "generalised de Bruijn" (bibliography);
  - "oppositely directed darts" (p.21);
  - "incidence defined by linear congruences" (p.57);
  - "The nonexistence of certain generalized polygons" (title of [148]).
- The only generalized-polygon content is the Feit–Higman exclusion in B2, which the survey uses to rule out bipartite Moore graphs for D ∉ {2,3,4,6}.
- Projective planes appear on p.33 (Singleton's equivalence) and p.36 (non-existence for orders 6 and 10). Refs: [296] H.J. Ryser, The existence of symmetric block designs, J. Combin. Theory Ser. A 32 (1982) 103–105 (the text says "Bruck, Ryser and Chowla's theorem"); [232] C.W.H. Lam, L. Thiel, S. Swiercz, Canad. J. Math. 41 (1989) 1117–1123.

## 4. Open problems that touch asymptotics (pp. 70–71)

- Problem 5 (p.70): restricted versions, "for vertex-transitive graphs, Cayley graphs, bipartite graphs."
- Problem 6 (p.70): the Bermond–Bollobás question (A9).
- Problem 7 (p.70): "Prove or disprove the conjecture of Bollobás (Subsection 3.3.1), stating that for each ε > 0, n∆,D > (1 − ε)∆^D, for sufficiently large ∆ and D." (A4)
- Problem 8 (p.70): "Is it true that n∆,D = vt∆,D, for infinitely many pairs of ∆ ⩾ 3 and D ⩾ 2?"
- Problem 14 (p.70): the existence of lim n∆,D(S)/∆^⌊D/2⌋ as ∆ → ∞ (A24).
- Problem 15 (p.71): "Are there any bipartite graphs of defect 2 when the diameter is 3?"

## 5. What the survey does not contain (answers to the brief)

- No lim sup anywhere. Every limit is a lim inf (µ_D on p.19, β_D on p.36).
- No statement that lim sup n_b/M_b = 1 for any D outside {2,3,4,6}.
- No octagon or generalized-octagon statement and no D = 8 asymptotic. D = 8 appears only in Table 4 (B8) and in the Feit–Higman exclusion of bipartite Moore graphs (B2).
- No flag-graph, building, Coxeter-group or unequal-(s,t) polygon result.
- No Kronecker-with-opposite-graph construction. Delorme's bipartite constructions are described only as "bipartite versions of ... ∗-product and compounding" (B7).

## 6. My arithmetic (not from the survey; verify before use)

(i) D = 8 ratios: see B8.

(ii) Generalized octagons. The standard point and line counts of a generalized octagon of order (s,t) are (1+s)(1+st+s²t²+s³t³) and (1+t)(1+st+s²t²+s³t³), from general knowledge and not from the survey. Its incidence graph therefore has V = (2+s+t)(1+st+s²t²+s³t³) vertices, diameter 8, and maximum degree max(s,t)+1. Checks: for s = t = q this gives V ≈ 2q⁷, matching the Moore bound (consistent with B2). For (s,t) = (2,4), V = 4680 (1755 points and 2925 lines).
- For (s,t) = (q, q²), a family I believe exists for q = 2^(2m+1) (Tits/Ree–Tits octagons, from general knowledge, not checked here), ∆ = q² + 1 and V ~ q^11 ~ ∆^5.5. So V / B_{∆,8} → 0. Numerically: q = 8 gives V/B = 0.0011, and q = 32 gives 1.6 × 10⁻⁵.
- Tentative conclusion: unequal-order octagons alone cannot give a positive lim inf ratio for D = 8. Any octagon route to β_8 = 1 would need s/t → 1 with s ≠ t. I did not check whether such parameters are possible.

(iii) Cayley bounds in A17 give liminf C/Δ^D at least 3/16, 32/625 and 25/1024 for D = 3, 4, 5. These are far below µ_3 = µ_5 = 1 for general graphs.

(iv) Planar: p∆,D ~ (3/2)∆^(D/2) from the text-layer formula in A22.

## 7. Score

S = 2. The survey gives explicit bipartite asymptotic statements with constants: β_D ⩽ 1 for all D with equality for D ∈ {2,3,4,6} (B5), and the normalization B_{∆,D} ~ 2∆^(D−1) (B1). It does not state lim sup n_b/M_b = 1 for any D outside {2,3,4,6}, and has no flag or building result, so S = 3 does not apply.

## 8. Caveats

- Formulas marked "text layer" were transcribed from the PDF text layer. Several have garbled superscripts or missing subscripts; see A11, A19, A20.
- Printed "D^1.525" (A19) and "D^2.525" (A20) are most likely typos for ∆.
- Ref [168] is printed as 1996 in the bibliography; I cite it as 1966 (EC-15) because the volume matches 1966.
- The 2026 preprints named in the brief (Cames van Batenburg–Korsky, Isham et al.) are not re-reported.
