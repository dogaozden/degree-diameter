# c5 notes: bipartite Coxeter element, subword property, building facts, diameter

Card c5, literature pass (time-boxed). Downloads and extracted text are in
/home/user/degree-diameter/research/squads/buildings-r1-lit/c5/dl/ (arXiv PDFs and pdftotext output).
Page numbers below are arXiv PDF pages unless stated.
Status labels: "verified" = text seen in the PDF; "cited" = number seen only as quoted by another paper; "unverified" = not seen.

Note: arXiv math/0111053 is Kaloshin, not Fomin–Zelevinsky. Fomin–Zelevinsky "Y-systems" is hep-th/0111053.

## (i) Alternating word of h segments is a reduced word for w0

**Best verified reference (1): Yang–Zelevinsky, "Cluster algebras of finite type via Coxeter elements and principal minors", arXiv:0804.3303v2, Lemma 2.3, p. 9 (verified).**

Quote: "Lemma 2.3. [4, Exercise V.6.2] We have t+ t− t+ · · · t± t∓ = w◦. Moreover, the word i◦ = i+ i− i+ · · · i± i∓ (concatenation of h segments) is a reduced word for w◦."

Setup on the same page: the Coxeter graph is a tree, so it is bipartite, I = I+ ⊔ I−; t± = product of the s_i over I±; t = t+ t−; h = Coxeter number. Reference [4] = N. Bourbaki, Lie Groups and Lie Algebras, Ch. 4–6 (Springer, 2002). Also p. 9: "h is even for all types except A_n with n even", and "If h is even, then Lemma 2.3 says that t^{h/2} = w◦."

**Second verified source (2): Fomin–Zelevinsky, "Y-systems and generalized associahedra", arXiv:hep-th/0111053v1, Lemma 2.1, p. 9 (verified).**

Quote: "Lemma 2.1. [5, Exercise V.§6.2] The word i◦ = i− i+ i− · · · i∓ i± (concatenation of h segments) is a reduced word for w◦."

Reference [5] = N. Bourbaki, Groupes et algèbres de Lie, Ch. IV–VI (Hermann, 1968). FZ's word starts with I−, Yang–Zelevinsky's starts with I+. The bipartition is only fixed up to renaming, so both starting classes are covered, which is what the task asks for.

**Third (verified text, Steinberg not seen): Brady–Kenny–Watt, "Climbing elements in finite Coxeter groups", arXiv:1005.0775v1, p. 3.**

Quote: "If w0 is the longest element of W then it follows from the proof of Corollary 4.5 of [10] that w0 has the reduced expression". The display that follows gives w0 = c^{h/2} if h is even, and w0 = c^{(h−1)/2} R(α1)…R(αs) if h is odd, where c = R(α1)…R(αn) is the bipartite Coxeter element. Their [10] = R. Steinberg, "Finite reflection groups", Trans. AMS 91 (1959) 493–504 (bibliography, p. 8). Steinberg's Corollary 4.5 itself: unverified.
The same paper, p. 3, also says Inv_ρ(w0) = {ρ1,…,ρ_{nh/2}} = Π+, which gives |Φ+| = nh/2. So the word in (i) has length nh/2 = ℓ(w0).

**Bourbaki Ch. V §6 Exercise 2:** the exercise text was not seen. Two papers (Yang–Zelevinsky and Fomin–Zelevinsky, above) cite it as Exercise V.6.2 / V.§6.2 for this lemma, so the location is consistent across two sources but not checked against Bourbaki.

Not checked (unverified): Humphreys §3.17–3.20; Steinberg 1959 itself; Kostant 1959; Lusztig 1976; Reading's c-sorting papers.

## (ii) Subword property of Bruhat order

**Best verified statement: Armstrong–Hersh, "Sorting orders, subword complexes, Bruhat order and total positivity", arXiv:0909.2828v2, p. 2 (verified).**

Quote: "u ≤Br v if and only if any reduced word for v has a subword that is a reduced word for u." The same page defines the Bruhat order by: "u ≤B v if there exists a reduced word for v such that u occurs as an arbitrary subword." This is the "any reduced word" form the proof needs, applied to the fixed reduced word i◦ of w0. The paper gives no Björner–Brenti theorem number.

**Book reference: Björner–Brenti, Combinatorics of Coxeter Groups, GTM 231 (2005).**
- Theorem 2.2.2 (subword property): unverified. The number was not seen in any downloaded text.
- MathWorld (secondary, https://mathworld.wolfram.com/Subword.html) gives "p. 34" for the criterion "u <= v iff a reduced word for u is a subword of a reduced word for v (Björner and Brenti 2005, p. 34)". This is a weaker quantifier (some reduced word of v), so it does not replace the Armstrong–Hersh form.
- Jahn–Stump, arXiv:2103.03715, cite BB05 Lemma 1.4.4, Prop. 2.2.7, Cor. 2.2.8 and Lemma 2.2.10 for Bruhat-order facts (verified citations). This fits Bruhat material in §2.2 but does not pin Theorem 2.2.2.

Other candidates (unverified): Björner–Wachs, "Bruhat order of Coxeter groups and shellability", Adv. Math. 43 (1982) 87–100, subword section (only a search snippet says §2.3); Humphreys §5.10.

## (iii) Building facts (W-metric)

Book: Abramenko–Brown, Buildings: Theory and Applications, GTM 248 (Springer, 2008). Chapter 5 is the W-metric chapter and the Weyl distance function is in §4.8. Both come from a library-catalogue snippet, not the book (unverified).

No numbered W-metric statement has been verified. The numbers below are cited only, not seen in AB08:
- Gate property in the Coxeter complex. Quoted in arXiv:1008.4908 (a dissertation, "Buildings, Group Homology and Lattices"), Proposition 3.1.19, PDF p. 37, citing "Proposition 3.103 and 3.105 in [AB08]": "Let σ ∈ Σ(W, S) be a simplex and let c ∈ Σ(W, S) be a chamber. Then there is a unique chamber e in the residue R_Σ(σ) called the projection of c onto R_Σ(σ) such that for any chamber d ∈ R_Σ(σ) there is a minimal gallery from c to d through e." This is the Coxeter-complex version, not the building one.
- Opposition: the same dissertation cites AB08 Lemma 5.111 (opposite chambers, spherical case) and §5.7.4 (opposite types via diagram automorphism). Cited only.

Standard facts with no verified numbered source (check AB08 Ch. 5 directly):
- For δ(C,D) = w and a reduced word for w, there is a gallery of that type from C to D (unique, minimal). The proof uses only the existence part.
- For residues of types J, K, the Weyl distances form the double coset W_J w W_K.

## Diameter statement

**Rank 2 (verified in the literature).** Parkinson–Temmermans–Van Maldeghem, "The combinatorics of automorphisms and opposition in generalised polygons", arXiv:1309.6190v3, p. 5: "The incidence graph of a generalised n-gon Γ = (P, L, I) is the graph with vertex set P ∪ L, and vertices x and y from an edge if and only if x I y. … The incidence graph of Γ has diameter n and girth 2n, and these properties actually characterise generalised n-gons." No proof is given there. The dissertation arXiv:1008.4908, Def. 4.1.2, PDF p. 58, has the same statement: a generalised m-gon is a building of type I2(m) whose incidence graph has diameter m and girth 2m. Since h(I2(m)) = m, this is the rank-2 case h = m.

**Type A (the sorting statement is verified; the reduction is mine).** Odd–even transposition sort: arXiv:1612.06473 p. 8, "It is known that after n rounds the pebbles in P_n are sorted [7]", and p. 2, "the odd-even transposition sort takes n matching steps (see, e.g., [7])". Reference [7] = D. E. Knuth, The Art of Computer Programming vol. 3 (Sorting and Searching); exercise number unverified. Habermann (1972) attribution is from Wikipedia (secondary, unverified).
Reduction (mine, not stated in these sources): for S_{n+1} with I_odd = {s_i : i odd} and I_even = {s_i : i even}, h = n+1. Each odd (or even) round is an element of W_{I_odd} (or W_{I_even}). So sorting any permutation of n+1 items in n+1 rounds shows every permutation is an alternating product of h = n+1 such factors.

**General type: not found.** Searches that found nothing: "bipartite Coxeter element ... longest element ... Coxeter number"; "every element of a finite Coxeter group is an alternating product of W_I and W_J"; "incidence graph spherical building diameter Coxeter number"; odd–even sort plus Coxeter/Weyl; "bipartite Coxeter" in arXiv abstracts (hits 1005.0775, 2009.03647, 2208.10464, none on this point). Nearest hits: Brady–Kenny–Watt (bipartite factorisation of w0, no diameter statement); Reading, arXiv:0912.5028 (bipartite Coxeter elements, Coxeter plane; no residue statement).

**Derivation I would propose (mine, to check).**
1. By (i), i◦ is a reduced word for w0 with h segments. Segment k is a set of distinct, pairwise commuting generators of one class.
2. Every w ≤ w0. By (ii), some subword of i◦ is a reduced word for w. Restricting it to each segment gives x_k ∈ W_{I±}, so w = x1⋯xh with alternating classes and length additive. The class-swapped word (also reduced for w0) gives the other starting class.
3. Building: for C ∈ A (type I1 residue) and D with δ(C,D) = w, (iii) gives a gallery C = C0, …, Ch = D with δ(C_{k-1}, C_k) = x_k. R_k = the residue of type of x_k containing C_{k-1}, C_k. Consecutive R_k share C_k, so they are adjacent in the incidence graph. The walk R_1 = A, …, R_h has length h−1, and one more step reaches B. So dist(A,B) ≤ h for any residues A, B. The lower bound (distance exactly h, attained) is not addressed in any source found. Rank 2 supports it.

## Gaps and next steps
- Bourbaki Ch. V §6 Exercise 2: exercise text.
- Björner–Brenti Theorem 2.2.2 (number and statement), and BB Lemma 1.4.4 / Prop 2.2.7 as cited by Jahn–Stump.
- Abramenko–Brown Ch. 5: numbered statements for minimal galleries, Weyl distances on residue pairs (double cosets), and the building-level gate property.
- General-type source for "every w is an alternating product of h factors from W_I1 and W_I2"; the type-A odd–even sort result is the nearest. Also the lower bound (distance h attained for general type).
- Knuth TAOCP vol. 3 exercise on odd–even transposition sort (number and worst-case statement).
