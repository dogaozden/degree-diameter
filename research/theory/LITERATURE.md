# Literature: what is already proved

theory job "cd-theory", 2026-10-23. Citations were checked this session against arXiv abstract pages, journal pages,
Crossref, zbMATH or DBLP.

**Tags.**
- **[V]** verified: the abstract or the theorem statement was seen.
- **[B]** bibliographic data verified, but the result was seen only second-hand or not at all.
- **[M]** from memory, not checked this session.

Statements are paraphrases unless in quotes.

## Bottom line

**No diameter-threshold theorem for random Haar (bi-Cayley) graphs, or for random group-voltage lifts of the
Δ-dipole, was found.** Searches covered: "random Haar graph diameter (threshold)", "random bi-Cayley graph
diameter", "bipartite Cayley graph random generating set diameter", "diameter of random lifts / random voltage
assignment", "random difference basis/cover threshold", and "Haar graph random subset S diameter/expansion whp".

The closest results are:
1. **Bollobás–Fernandez de la Vega (1982)**: random regular graphs, the coupon-collector diameter law, with constant 2.
2. **Christofides–Markström (2014)** and **Christofides–Markström–Savvidou (2026 preprint)**: diameter thresholds of
   random Cayley graphs in the many-generators (p-random) model. Their constants are group-dependent.
3. **Yadin (2009)**: a sharp threshold √(Θ(G) n log n) for random sets A, B with AB ∪ BA = G, proved with Suen's
   inequality. This is the same scale and the same tool as our D = 3 case.

None of them covers Haar graphs, bipartite alternating words, the special-target/odd-D phenomena, or the
fixed-Δ regime. **Before calling THRESHOLD.md Theorems 3–4 new, read Christofides–Markström–Savvidou
arXiv:2605.29457 in full.** It is the nearest neighbour; it appeared in May 2026 and was seen only via its abstract.

## 1. Random regular graphs (the analogue Kenan cited)

1. **B. Bollobás, W. Fernandez de la Vega, "The diameter of random regular graphs", Combinatorica 2(2) (1982)
   125–134, doi:10.1007/BF02579310.** [B]
   - Abstract: "asymptotic upper and lower bounds for the diameter of almost every r-regular graph on n vertices."
   - Second-hand statement (Wikipedia; Shimizu, METR 2017-19): if d is least with (r−1)^{d−1} ≥ (2+ε) r n ln n, then
     a.a.s. diam ≤ d. The lower bound is about ⌊log_{r−1} n⌋ + ⌊log_{r−1}((r−2) ln n/(6r))⌋.
   - **Not read in the original.** Check before quoting a constant or an off-by-one.
   - The constant 2 here, versus our 1, is SIZE_LAW §2.4's "factor 2 in the log". A random regular graph must
     connect all ~n² pairs; a Haar graph is transitive on each side, so ~n targets suffice.
2. **D. Fernholz, V. Ramachandran, "The diameter of sparse random graphs", RSA 31(4) (2007) 482–516,
   doi:10.1002/rsa.20197.** [V]
   - Diameter c ln n + o(ln n) for random graphs with a given degree sequence.
   - No explicit statement for random bipartite d-regular graphs or unions of d random perfect matchings was found.
   - Bollobás–Klee (Combinatorica 4 (1984) 7–19) is about binomial random bipartite graphs, not regular ones. [B]

## 2. Random Cayley graphs

3. **D. Christofides, K. Markström, "The thresholds for diameter 2 in random Cayley graphs", RSA 45(2) (2014)
   218–235, doi:10.1002/rsa.20486, arXiv:1108.3547.** [V]
   - Model: each element is a generator independently with probability p.
   - For any group, diam ≤ 2 whp if p ≥ √((2+ε) log n/n), and diam > 2 if p ≤ √((1/4−ε) log n/n).
   - The constant depends on the group: 2 for Z_2^n, 1/2 for cyclic groups, 1/4 for symmetric groups.
   - Companion: "The range of thresholds for diameter 2 in random Cayley graphs", Eur. J. Combin. 35 (2014)
     141–154. Every value in [1/4, 1/2] occurs. [B]
   - *Relevance:* the group dependence of the constant parallels THRESHOLD §3 (involutions, centre, abelian
     coincidences).
4. **D. Christofides, K. Markström, M. Savvidou, "Diameter thresholds of random Cayley graphs", arXiv:2605.29457
   (May 2026).** [V, abstract only]
   - Range 2 ≤ d ≤ (1−γ)√(log N/(2 log log N)).
   - diam ≤ d whp if p ≥ ((1+ε) d! log N / N^{d−1})^{1/d}.
   - diam > d whp if p ≤ ((1−ε) 2^{−d} log N / N^{d−1})^{1/d}.
   - Both are sharp for suitable families.
   - It covers Cayley graphs, not Haar graphs. Its window, d! versus 2^{−d}, has the same shape as our
     Corollary 4.2 window [1, (D−1)!] in units of n ln n. **Closest existing work.**
5. **G. Yadin, "When do random subsets decompose a finite group?", Israel J. Math. 174 (2009) 203–219,
   arXiv:0712.3019.** [V]
   - With A, B random k-subsets: AB ∪ BA = G whp above (1+ε)√(Θ(G) n log n), and fails below (1−ε)√(Θ(G) n log n).
   - Θ(G) ∈ (1/2, 1], equal to 1 iff G is abelian.
   - Uses Suen's inequality. Our Lemma 2.2 uses Yadin's stated form.
6. **N. Alon, Y. Roichman, "Random Cayley graphs and expanders", RSA 5(2) (1994) 271–284,
   doi:10.1002/rsa.3240050203.** [V] c(δ) log n random elements give an expander whp. Essentially tight for abelian
   groups.
7. **J. Hermon, S. Olesker-Taylor.** [V]
   - "Geometry of random Cayley graphs of Abelian groups", Ann. Appl. Probab. 33(5) (2023) 3520–3562,
     arXiv:2102.02801.
     - k uniform generators with 1 ≪ log k ≪ log|G|.
     - The distance from the identity concentrates at the minimal radius M of a ball in Z^k with ≥ |G| points, for
       all but o(|G|) elements.
     - When k ≳ log|G|, the diameter is also ~M.
   - "Cutoff for almost all random walks on Abelian groups", JEMS 28(5) (2026) 1913–1977, arXiv:2102.02809.
   - "Further results and discussions on random Cayley graphs", arXiv:1911.02975.
   - *Relevance:* the abelian case. Their Z^k-ball radius is the analogue of our Theorem 2 count A(Δ,D).
8. **J. Marklof, A. Strömbergsson, "Diameters of random circulant graphs", Combinatorica 33(4) (2013) 429–466,
   arXiv:1103.3152.** [V] For fixed k, a random 2k-regular circulant has diameter of order n^{1/k}, with a limit law.
9. **G. Amir, O. Gurel-Gurevich, "The diameter of a random Cayley graph of Z_q", Groups Complex. Cryptol. 2(1)
   (2010) 59–65, arXiv:math/0609620.** [V] With k fixed generators the diameter is Θ(q^{1/k}).
   - Items 8–9 are the abelian obstruction for fixed Δ: polynomial, not logarithmic, diameter. Compare our
     Theorem 2, n ≤ |G'|·O(D^{Δ−1}).
10. **S. Eberhard, U. Jezernik, "Babai's conjecture for high-rank classical groups with random generators",
    Invent. Math. 227(1) (2022) 149–210, arXiv:2005.09990.** [V] Random generators in high-rank classical groups
    give polynomial diameter. Not our regime.
11. **I. Pak**, random Cayley graphs with O(log|G|) generators (ESA 1999). [M] Not checked; not used.

## 3. Haar graphs, bi-Cayley graphs and the degree-diameter problem

12. **M. Hladnik, D. Marušič, T. Pisanski, "Cyclic Haar graphs", Discrete Math. 244(1–3) (2002) 137–152.** [B]
    The name and the basic theory of cyclic Haar graphs.
13. **A. Estélyi, T. Pisanski, "Which Haar graphs are Cayley graphs?", Electron. J. Combin. 23(3) (2016) #P3.10,
    doi:10.37236/5240, arXiv:1505.01475.** [V] For example, every Haar graph of D_{2n} is Cayley iff n ∈ {2,3,4,5}.
14. **A. Agarwal, K. Chandrasekaran, A. Kolla, V. Madan, "On the expansion of group-based lifts", SIAM J. Discrete
    Math. 33(3) (2019) 1338–1373, arXiv:1311.3268.** [V] Spectral results for random group-based lifts; abelian lifts
    are never almost-Ramanujan. Nothing on diameter. (A Haar graph is a G-lift of the Δ-dipole.)
15. **M. Miller, J. Širáň, "Moore graphs and beyond: A survey of the degree/diameter problem", Electron. J. Combin.
    Dynamic Survey DS14, 2nd ed., 16 May 2013.** [B] Source of our table (TABLE.md) and of the bipartite Moore bound
    2Σ_{i<D}(Δ−1)^i.
16. **W. Feit, G. Higman, "The nonexistence of certain generalized polygons", J. Algebra 1(2) (1964) 114–131.** [B]
    Thick generalized n-gons exist only for n ∈ {2,3,4,6,8}. Hence there are no bipartite Moore graphs for D ≥ 7 with
    Δ ≥ 3.
17. **J. Singer, "A theorem in finite projective geometry and some applications to number theory", Trans. AMS 43(3)
    (1938) 377–385, doi:10.1090/S0002-9947-1938-1501951-4.** [B] Cyclic difference sets. The Haar graph
    H(Z_{q²+q+1}, Singer set) attains Theorem 1 at D = 3.

## 4. Expansion, girth and diameter for SL(2,q) with random generators (the fixed-Δ regime)

18. **J. Bourgain, A. Gamburd, "Uniform expansion bounds for Cayley graphs of SL_2(F_p)", Ann. of Math. 167 (2008)
    625–642.** [V] Random generators, as well as projections of a fixed non-elementary subset of SL_2(Z), give
    expanders. Consequence: diam = O(log p) with an unspecified constant.
19. **H. A. Helfgott, "Growth and generation in SL_2(Z/pZ)", Ann. of Math. 167 (2008) 601–623, arXiv:math/0509024.**
    [V] Every generating set gives diameter O((log p)^c).
20. **E. Breuillard, A. Gamburd, "Strong uniform expansion in SL(2,p)", GAFA 20(5) (2010) 1201–1209,
    arXiv:0911.3022.** [V] There is a density-one set of primes on which all Cayley graphs of SL(2,p) are uniform
    expanders.
21. **A. Gamburd, S. Hoory, M. Shahshahani, A. Shalev, B. Virág, "On the girth of random Cayley graphs", RSA 35(1)
    (2009) 100–117, arXiv:0707.1833.** [V] For fixed Lie type and rank, the girth is ≥ (1/dim G − o(1))·log_{d−1}|G|
    a.a.s. That is 1/3 for SL_2.
22. **A. Lubetzky, Y. Peres, "Cutoff on all Ramanujan graphs", GAFA 26(4) (2016) 1190–1216, arXiv:1507.04725.** [V]
    On any Ramanujan graph, every vertex is at distance (1+o(1)) log_{d−1} n from n − o(n) vertices.
    - *Typical* distance only, and only for Ramanujan graphs.
    - Random Cayley graphs of SL(2,p) are not known to be Ramanujan.
23. **N. T. Sardari, "Diameter of Ramanujan graphs and random Cayley graphs", Combinatorica 39(2) (2019) 427–446,
    arXiv:1511.09340.** [V]
    - Bipartite LPS graphs have diam ≥ (4/3) log_p n − O(1).
    - For random Cayley graphs of PSL_2(Z/q): **numerics only**, suggesting diam ~ log_{k−1} n. Nothing proved.
    - *Relevance:* our Conjecture 6 sharpens this numerical observation to log_{Δ−1} n + log_{Δ−1} ln n + O(1),
      for Haar graphs.

**State of the art for fixed Δ.** log_{Δ−1} n − O(1) ≤ diam ≤ C log n, with C unspecified. The constant 1 is
**open**.

## 5. Quasirandom groups, product mixing, word maps

24. **W. T. Gowers, "Quasirandom groups", CPC 17(3) (2008) 363–387, arXiv:0710.3877.** [V]
    - If no nontrivial representation has dimension < m and |A||B||C| > n³/m, then ab = c is solvable.
    - Lemma 5.1, specialised: |G ∖ AB^{−1}| ≤ n³/(m|A||B|).
25. **N. Nikolov, L. Pyber, "Product decompositions of quasirandom groups and a Jordan type theorem", JEMS 13(4)
    (2011) 1063–1077, arXiv:math/0703343.** [V] |A||B||C| > n³/m implies ABC = G.
26. **L. Babai, N. Nikolov, L. Pyber, "Product growth and mixing in finite groups", SODA 2008, 248–257.** [B; snippet]
    The L² mixing bound ‖XY − U‖ ≤ √(n/m)‖X‖‖Y‖.
    - *Use for us:* deterministic, any S. If two sub-balls of the word tree are nearly full, they cover all but
      n³/(m|A||B|) elements. For SL(2,q), m ≈ q/2, this gives only diam ≲ (8/3) log_{Δ−1} n under full-ball
      (girth) assumptions, which random S do not satisfy at that radius. Much weaker than the random theory.
27. **M. Larsen, A. Shalev, "Word maps and Waring type problems", JAMS 22(2) (2009) 437–466, arXiv:math/0701334.**
    [V] Results on images of word maps. The proof of Prop. 2.1 contains the point count |V(F_q)| ≤ c·q^{dim V} that
    Lemma 5.1 uses.
28. **M. Larsen, A. Shalev, "Fibers of word maps and some applications", J. Algebra 354 (2012) 36–48.** [V] For
    w ≠ 1 there is ε > 0 with |w^{−1}(g)| = O(|G|^{d−ε}) for all finite simple G and all g.
29. **M. Larsen, A. Shalev, P. H. Tiep, "Probabilistic Waring problems for finite simple groups", Ann. of Math.
    190(2) (2019) 561–608, arXiv:1808.05116.** [V]
    - Products of words in disjoint variables are almost uniform in L¹.
    - A product of O(l⁴) words of length ≤ l is almost uniform in L∞.
    - *Relevance:* almost-uniformity of single word maps, in fixed or bounded length. Our fixed-Δ conjecture needs
      joint statements for ~log n-length words, far beyond this.
30. **A. Borel, "On free subgroups of semisimple groups", Enseign. Math. (2) 29 (1983) 151–164.** [B] Word maps on
    semisimple algebraic groups are dominant. This is the attribution given by Larsen–Shalev and by
    Gordeev–Kunyavskii–Plotkin; the zbMATH review mentions only the free-subgroup theorem. Used in Lemma 5.1.
31. **N. Gordeev, B. Kunyavskii, E. Plotkin, "Word maps, word maps with constants and representation varieties of
    one-relator groups", J. Algebra 500 (2018) 390–424, arXiv:1801.00379.** Also Doklady Math. 94(3) (2016) 632–634.
    [V]
    - Words with constants w₁σ₁w₂⋯σ_r w_{r+1} are dominant for generic constants, but not always; x σ x^{−1} is the
      standard exception.
    - *Relevance:* gap G1 in THRESHOLD.md is a non-degeneracy statement of exactly this kind, for specific
      constants (the target x).

## 6. Probabilistic tools

32. **S. Suen, "A correlation inequality and a Poisson limit theorem for nonoverlapping balanced subgraphs of a random
    graph", RSA 1(2) (1990) 231–242.** [B]
33. **S. Janson, "New versions of Suen's correlation inequality", RSA 13(3–4) (1998) 467–483.** [B]
    - The commonly quoted form P(X = 0) ≤ exp(−μ + Δe^{2δ}) was **not** confirmed from the paper.
    - Theorem 3 there, P(X = 0) ≤ exp(−min(μ²/8Δ, μ/2, μ/6δ)), was confirmed second-hand.
    - THRESHOLD.md Lemma 2.2 uses Yadin's verified form instead (item 5).
34. **P. Erdős, L. Lovász (1975)**; **N. Alon, J. Spencer, *The Probabilistic Method*, Lemma 5.1.1** (asymmetric LLL).
    [M] Standard.

## 7. Answer to "does a random Haar graph threshold theorem already exist?"

**Not that I could find.**
- Its two ingredients exist separately:
  - coupon-collector diameter thresholds for random *Cayley* graphs with many generators (Christofides–Markström;
    the 2026 preprint with Savvidou);
  - Suen-inequality thresholds for random product sets (Yadin).
- In the bipartite/Haar setting, THRESHOLD.md Theorems 3–4 (any group, D fixed) and Corollaries 5.2–5.3 (PSL and
  PGL at odd D; abelian groups) appear to be new. **Confirm against arXiv:2605.29457 before claiming this.**
- In the fixed-Δ regime of our records, nothing comparable is known even for Cayley graphs. The best rigorous
  results are an O(log n) diameter from expansion, and numerics (Sardari).
