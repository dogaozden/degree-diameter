# Referee report: "Large bipartite graphs of given degree and diameter from generalized polygons"

Draft of 28 October 2026 by G. Araujo-Pardo, N. López and D. Özden: `research/paper/joint.tex` and `joint.pdf` (56 pages),
branch `claude/joint-paper-draft-07dyt1`, commit `aa07b20`. I read the paper as an outside referee for a combinatorics
journal and did not use the lab's notes. Numbers of theorems, tables and pages are those of the compiled PDF. (The PDF's
numbering differs from the `\label`s in places: for example Theorem R is Theorem 5.18, Corollary C1 is Corollary 4.12, the
hub-graph lemma is Lemma 6.19 and the classical diameter-7 bounds are Corollaries 6.20–6.23.)

Severity tags: **error** = a statement that is false as written; **gap** = a statement that is not proved in the text, or
whose proof depends on something the reader cannot see; **presentation** = correct but should be changed.

I recomputed by my own short scripts everything I could rebuild from the paper's text. The scripts and their log are in
`research/referee/joint-paper-checks/` (`run_all.sh`, `run.log`; the q = 7 and q = 8 hexagon runs are in `d6_q7.log`,
`d6even_q8.log`). They do not reuse the lab's builders or the draft's `checks/` scripts. A summary is in Part 8.

## Summary of the paper and recommendation

The paper improves lower bounds for n_b(Δ, D) in the 2013 table of Miller and Širáň in many cells: at D = 3, 4, 6 by
explicit constructions from PG(2, q), generalized quadrangles and H(q) (a fourth "hat", clones and shadow lines with a
weighted 2-ovoid of AS(q) and Singer 2-ovoids of W(3, q), "whiskers" added to Delorme's doubling of H(q)); at D = 7 by a
general theory of 2r+1 copies of the incidence graph of H(q) joined by matchings, with deleted matching edges and new
"hub" vertices; at D = 5 and D = 8–10 by explicit Haar graphs found by computer. It also argues that six D = 8 entries of the
2013 table (Gómez's compound graphs) have diameter at least 9 as defined.

The mathematics is in good shape. I found no false theorem, lemma or formula. Every construction I rebuilt from the printed
definitions has the stated order, maximum degree and diameter, and every number in the tables that follows from a formula
recomputes. The main problems are elsewhere:

1. the abstract overstates how explicit the constructions are (point 1), and several record values rest on data that
   the paper does not print (points 5, 6, 23);
2. the paper is really four papers (D = 3/4/6 constructions; the D = 7 theory; a critique of the D = 8 table entries;
   a computer catalogue of Haar graphs), plus long appendices on Lean and on computer checks. At 56 pages with 31 open
   `\todo` notes it is not yet a submission;
3. the prior-work sections are written as reports of a literature search ("the searches we made returned nothing")
   rather than as a review of the literature, and some credits are missing or need checking (Part 6);
4. notation is heavily overloaded across sections (Part 4).

Recommendation: major revision. I would split the paper (point 38) and, in the main paper, keep the results whose
ingredients are printed in full.

## Part 1. Statements that are false or not proved

**1. error — Abstract (p. 1): "All constructions are given in projective coordinates with the exact neighbourhood of every
new vertex."** This is false for several results that the abstract itself announces:
- the regular graphs of Theorem 5.18 (the "regular version" at D = 6, and the "reg." column of Table 1 at D = 6): the
  completing anti-flags exist by Lemma 5.17, but no rule is given (the text after Theorem 5.18 says so);
- the D = 7 values of Table 1 (Corollaries 6.24–6.26): the freed sets, the matchings away from the freed sets, the hub
  slots and the hub graphs are given only as data files (Section 6.9 says so);
- Corollaries 6.21 and 6.25 use a duality of H(3^h) for which no formula is given (the todo before Corollary 6.21);
- all Haar graphs of Table 8 except Example 8.5 and the two D = 5 graphs of Section 8.2: the connection sets are "given as
  data"; the (3,8) lift is described by its base graph and group, but its voltages are not given;
- Corollaries 6.20–6.23 leave the bijection away from R, the hub slots and the pendant attachments free. This is a legitimate
  "for every choice" statement, but it is not "the exact neighbourhood of every new vertex".

Fix: restrict the sentence to what is true (D = 3, 4, 6 without the regular completion at D = 6, and the classical D = 7
bounds up to the stated free choices), or print the missing data (see Part 3, where I list what would fit in an appendix).

**2. error (overstatement) — Abstract: "we prove which sets are allowed" (D = 7).** The paper proves sufficient conditions
(Theorems 6.12 and 6.15) and a converse only for automorphic transitions (Remark 6.13). For a non-automorphic transition,
(H1)–(H3) are not shown to be necessary; Proposition 6.16 only says what they imply. The Results paragraph in Section 1
states this correctly ("two sufficient conditions ..., the first also necessary"). Use the same wording in the abstract.

**3. gap — Lemma 5.6 (a), (b), (d) and Lemma 5.12 (a), (b), (d), p. 22–24: for z ≠ 0 the proof is "verified by direct
expansion (and checked by computer algebra)", and only z = 0 is printed.** The reader cannot check the general case without
a computer, and the claim in Section 1 that every theorem of Sections 2–7 "has a complete proof here" does not hold for
these two lemmas as printed. I checked the identities symbolically (`jz_sym.py`: all true, odd q over Z[x, α, β, c], even
q over F_2[δ, α, β, x]). There is a short structural proof, which also answers the todo before Lemma 5.7. For odd q let
g_z be the collineation (v, a, w) ↦ (A v, a, A^{-T} w) of Fact 2.3 with

  A^{-1} = [[1, 0, α], [−β/c, 1, 0], [0, 0, 1]]   (det = 1),

and for even q the same with A^{-1} = [[1, 0, α], [β/δ, 1, 0], [0, 0, 1]]. Then g_z maps Π onto Π_z, and
**J_z = g_z J_0 g_z^{-1}** on Π_z, exactly for the J_z printed in Sections 5.3 and 5.5 (both facts checked symbolically in
`jz_conj.py`). Since g_z preserves Q and maps lines of H(q) to lines of H(q), parts (a) and (c) for every z follow from
z = 0; part (b) is then not needed for z ≠ 0 (it is used only to prove (c)), and part (d) is a statement about z = 0 only.
I suggest printing g_z, the z = 0 expansions, and this paragraph instead of the general-z expansions.

**4. gap — Corollary 6.22 (p. 34): "The minimum is κ(q−2) for q ≤ 13 and (q+2)(q^2+1) for q ≥ 16."** The second half is
not proved. It is true for every prime power 16 ≤ q < 200 (I checked with the definition of κ), and for q ≥ 44 it
follows from κ(δ) ≥ (s^2+s+1)(1+(δ−s−1)δ) with δ = q−2 and s the largest power of 2 at most δ/2 (then s > δ/4, and
δ^3(δ/2−1)/16 ≥ (q+2)(q^2+1) for δ ≥ 42); add this argument and the finite check. The bound itself (with the min) is proved, so this only affects the sentence.

**5. gap — Corollaries 6.24, 6.25, 6.26 and Remark 6.27 are stated like theorems ("Values: ... order 23 598"), but each value
depends on an unpublished finite object whose properties are computer-checked:** the 81-, 295-, 229- and 768-element mirrored
sets; the friendly sets of 8645, 8246, 14 762 and 14 823 elements; the hub graphs (for (11,7) "a Haar graph of Z_73 ⋊ Z_100
of diameter 7", where neither the action defining the semidirect product nor the connection set is given; for (12,7) a Haar
graph of (Z_73 ⋊ Z_8) × Z_5^2 for which "(HG) holds using paths through the levels", with no argument). Section 6.9
says this in general terms, but each corollary should say which statement is computer-checked and name its data file, as
the paper promises in Section 1 ("we name the check"). Better, state the general results as theorems and list the values in
a table of computer-checked examples. Part 3 suggests what could be printed.

**6. gap — Corollary 6.24 (p. 35): "For q = 7, 11 the partial ovoid R_0 is an orbit of the Weyl group W(E_7) acting on
Q(6,q) through the E_7 root lattice modulo q."** This is not a definition a reader can use: which lattice, which quadratic
form, which embedding into Q(6, q), which orbit? (The todo after it says the same.) Either write it out (it would make R_0
explicit, which is valuable) or drop the sentence.

**7. gap — Section 7 (p. 37): the readings of Gómez's Figs. 2.21a/b.** Everything in Section 7 depends on Definition 7.1
being Gómez's construction, and the paper's description of the two figures is in words ("the K_1-vertex k lies on the
pentagram edge between copies k−1 and k+1 ..."). The thesis is hard to obtain. Reproduce the two figures (redrawn) so that a
reader can check the transcription; without them the identification cannot be verified. Also say explicitly that the six
2013 entries are identified with Ω_q by their orders, which coincide with the values listed on p. 46 of the thesis (the
abstract says "the graphs of Gómez behind six diameter-8 entries", which is an inference from the orders and the credit).

**8. gap — Remark 3.5 (p. 13) asserts an error in [AL20] (the index set of the completing matching) from arXiv v1 only.**
A referee of this paper cannot check this either. Check it against the journal version (Graphs Combin. 38 (2022), Paper
110) or remove it; if it stays, it belongs in a footnote, and the authors of [AL20] are co-authors here, so the remark can
simply say "corrected here".

**9. gap — Section 2.3 (p. 8): duplicates "(see [DF84], which we have not seen, and [D85a, §7])".** A paper should not cite
a reference the authors have not read. Check [DF84] or cite only [D85a]. The same applies to the place in [VM98] for the
form of Tits' equations (the todo in Section 2.2): the citation must be checked before submission.

**10. gap (minor) — Lemma 7.20 (p. 45) uses "for a quadratic form of rank r on F^7 (q odd), |Σ_v ψ(R(v))| = q^{7−r/2}"
and Fact 7.16 (eigenvalues in G_2) without references.** Both are standard; cite a source (for example Lidl–Niederreiter
for the Gauss sum, and any text on G_2 or the structure of its maximal torus). I checked the bound of Lemma 7.20 at q = 7 on
twelve fixed-point-free elements of the SL(3, 7) subgroup of G_2(7): the largest |Perp(h)| was 2850, below 4144
(`perp_ref.py`).

**11. presentation (borderline error) — Fact 2.3: "for q prime every collineation is a linear map in G_2(q) ≤ SO(7,q)".**
For q = 2 the polar form of Q is degenerate and "SO(7,2)" needs explanation. The fact is used only at q = 7; say "for q an odd
prime".

Claims about the literature are treated in Part 6: n_b(7,3) = 80 and the credit for 190 at (11,3) are right (point 34), the
sentence on the wiki's changes since 2013 is right (point 27), the credit for the non-existence of ovoids of Q(6,q) is
incomplete (point 30), and the girth-30 statement is right (point 32).

## Part 2. Proofs that are hard to follow, and what would fix them

**12. presentation — Lemmas 3.3 and 3.4.** The case analysis is correct (I rebuilt S(q; a, c) from (C1)–(C6) for every prime
power q ≤ 13 and every admissible (a, c) for q ≤ 9: diameter 3 in all cases), but it is long and leans on (F1)–(F4)
implicitly. A table "pair type → a common line (point)" would be easier to check than the prose. Since the correlation δ
already maps the σ-structure to the dual of the σ^{-1}-structure (end of Section 3.4), Lemma 3.4 can be deduced from
Lemma 3.3 in one paragraph.

**13. presentation — Proposition 4.10.** Part (a) is immediate from Ebert [E85]: each C_a is an elliptic quadric, hence a
cap. Cite this and keep only the proof of (b). In (b), define k' and the bar involution before the proof, say where q odd is
used, and add one sentence on why the zeros (s:t) of f_ν are exactly the points of L in C̃_μ (it uses N(u) ≠ 0). (The proof
is correct: for q = 3, 5, 7 exactly the pairs {a, q−a} give 2-ovoids, and the more general claim in Remark 4.11 holds in all
cases I tried, `singer_ref.py`.)

**14. presentation — Theorem 5.3, last paragraph.** "The diameter is exactly 6: a free point p (level −1) has q^5 opposite
points ..." is longer than needed: any two opposite points x, y of H(q) give d(x^w, y^u) ≥ 6 by the projection
x^w ↦ x stated after Definition 2.5.

**15. presentation — Theorem 7.5.** The sets A and B are upper bounds obtained by replacing walks by distances; say so. As
defined, B sums over e_1+e_2+e_3 ≤ 2 and includes the total 1, which cannot occur (e is even); this is a harmless overcount
(the even-sum bound is 6q^2+9q+4), but a reader will stop at it. State that the count is a union bound over pairs
(resp. triples) of distances.

**16. presentation — Section 7.4 (relabelling) is the hardest part of the paper.** The definitions (transfers, normal form,
the three kinds of pairs in W_2 of Lemma 7.11, starved pairs) are correct but need a picture of the wiring and a small table
of the route types (r = 2, 3, 4 copies; the order of point-bar and line-bar passes; which ball each produces). The q = 7
argument (Lemmas 7.17–7.20, Table 7, Theorem 7.21) should open with its strategy in two sentences: double-count the
perpendicular pairs among t, y_1, ..., y_5 over all points t, and compare with the character-sum bound of Lemma 7.20.

**17. presentation — Fact 7.14 should be replaced by a table and the definition it rests on.** It is a finite enumeration
over 2^α block patterns of the definitions in Lemma 7.11 and does not depend on q. I reproduced it from those definitions in
about 60 lines (`d8_lemmas.py`): every pair has r_4 ≥ α; the largest m_2 over starved pairs is 140 (α = 5), 201 (α = 6),
272 (α = 7), 353 (α = 8); the best starved pair in the worst pattern has m_2 = 134, 197, 262, 347. These agree with Fact 7.14.
A four-row table with these numbers, and the remark that they are a direct enumeration of Lemma 7.11, is a better form than a
"computer-checked fact" (this answers the todo after Fact 7.14).

**18. presentation — Lemma 5.7 and Lemma 5.13.** "Expanding, den(X) = ... and num(X) = ..." hides the only non-trivial
computation of the proof; give one intermediate line (the products X_2X_3 and X_4X_5 in terms of γ, β and p). I checked the
identity numerically for every free point p and every z in A_p for q = 3, 5, 7 (odd) and q = 4, 8 (even): no failure.

## Part 3. Does each construction give the exact neighbourhood of every new vertex, in coordinates?

| construction | explicit? | comment |
|---|---|---|
| Fourth hat, Definition 3.1, Table 2 | yes | Table 2 agrees with (C1)–(C6) row by row (`hat4_ref.py`, q ≤ 9 all (a, c), q = 11, 13 three (a, c) each). The filler is explicit. The coordinate-free version also works at q = 3 (5-regular, 36 vertices), as claimed. |
| Theorem 4.2, Table 3 | yes (general) | |
| Corollary 4.8 (AS(q)) | yes | The "New vertices" paragraph writes N(w) for the anisotropic form 𝗇(w) (p. 16); fix. |
| Corollary 4.12 (Singer) | almost | Clones and shadow lines are explicit. The regular completion says "any numbering"; fix one (for example the clone of ⟨g^i⟩ ∈ C_a ∪ C_{q−a} in increasing i, and the two copies of the spread line yK through ⟨g^j⟩, 0 ≤ j ≤ q^2, as y_{2j}, y_{2j+1}). |
| Corollary 4.13 | no | for q even an ovoid and a spread of W(3, q) are cited, not given; no table cell depends on it. |
| Example 4.6, Appendix A | yes | the 21 rows are lines of Q(4,5), they meet only as stated, and the graph has 359 vertices, maximum degree 7, diameter 4 (`app359_ref.py`). "What to check by hand" should also say that the six points of each row are collinear on Q(4,5); being on the quadric is not enough. |
| Theorem 5.3/5.8 (whiskers), Table 4 | yes | via Theorem 5.5 and Lemma 5.6(c) (the S_z lines are ⟨x, J_z x⟩). |
| Theorem 5.18 (regular, D = 6) | **no** | completion by Lemma 5.17 only. The todo calls an explicit completion "open work"; then the abstract and Table 1 must not suggest otherwise. |
| Corollaries 6.20, 6.22, 6.23 | up to free choices | fine as stated ("every choice gives the stated bound"). |
| Corollaries 6.21, 6.25 | **no** | a duality of H(3^h) is used without coordinates. The todo before Corollary 6.21 already points to the coordinatization of [VM98], in which the duality can be written down; do so, or at least give the map for q = 9 as data with a check that a reader can repeat. |
| Corollaries 6.24–6.26 (records) | **no** | data only. Much of it could be printed: the friendly sets are unions of orbits of an element of order q^2+q+1 (q = 11: 8645 = 65·133 and 8246 = 62·133; q = 13: 14 762 = 242·61 and 14 823 = 243·61), so orbit representatives would fit on a page; the mirrored sets have 81–768 elements; the Haar hub graphs need only their groups (with the action) and connection sets. |
| Section 7 (Ω_q) | yes | it is not a new construction. The labellings of Ω_2 and Ω_3 with diameter 8 (Section 7.5) are data only. |
| Haar graphs, Section 8.2 and Example 8.5 | yes | |
| Haar graphs, Table 8 | **no** | connection sets as data; the (3,8) lift has no voltages. A table of connection sets would take 2–3 pages, which is acceptable for an appendix. |

## Part 4. Notation and consistency across sections

**19. presentation — overloaded symbols.** The same letter is used for unrelated objects, often within a few pages:
- N: N(q) = (q+1)(q^4+q^2+1) (Sections 2, 5–7); N_0 (Section 3); N(g, A) (neighbourhoods, Section 8); N(X, c') (copies,
  Section 7.4); N_X(a, j) (Section 6.2); and **in Section 7.1 (p. 37) "ΩB_1 has N = 5(α+1)N_1" where N is the order and
  N_1 = 2N(q)** — this sentence reads as N = 5(α+1)·2N. Rename the order.
- Π: the hyperplane Π_z (Section 5) and the plane ⟨y, y', t⟩ (Lemma 7.17).
- σ: the 3-cycle (Section 3), the bijection P → L of Proposition 6.17 used in Corollaries 6.20–6.26, and L_0P_0^{-1}
  (Section 7.1).
- S: the incidence structure 𝒮, the set {0, 1, a, c}, the Hermitian spread S and S_z, the connection set S ⊆ G, the
  Bonferroni sums S_k; Σ is a spread in Section 4 and a 3-space Σ_0 in Section 6.
- W: the quadrangle W(3, q), the whisker set, the Weyl group W(E_7), the set W_2 of pairs of copies.
- δ: the trace-1 element (Section 5.5), the correlation of Section 3.4, the hub-graph degree (Section 6.7), a duality
  (Lemma 7.9(b)).
- κ: the quadric parameter (Theorem 4.7), the hub-graph size κ(δ) (Section 6.7), and D = 2κ (Theorem 8.4).
- α, β: the coordinates of z (Section 5), the slot counts α_j, β_j (Section 6), α = ⌊(q+3)/2⌋ and β ∈ {0,1} (Section 7),
  the automorphism α of Example 8.5.
- τ: types τ_j (Section 6), block types τ_B (Section 7), the involution τ (Theorem 7.5), and τ = y z̄ + ȳ z (Proposition 4.10).
- m: the doubling multiplicity, the number of elements freed on each non-friendly transition (Section 6.6), m(ν), m_c(t),
  m_2, and the mid-line m in Proposition 6.16.
- R: R(q; a, c), the freed sets R_t, the q lines R in the proof of Theorem 5.18, R_3 in Lemma 7.19, R_γ in Lemma 7.20.
At least N, Π, σ, S/Σ and δ should be renamed; a table of notation at the end of Section 2 would help.

**20. presentation — smaller inconsistencies.**
- The macro `\Om` prints "ΩH_q", which reads as Ω applied to a graph H_q, while the hexagon is H(q) everywhere else. Write
  Ω(H(q)) or Ω_q.
- n_b, M_b versus N^b (todo in Section 1): use the notation of [MS13] or [AL20].
- "Hat lemma" (Lemma 2.7) is about trees in the doubled set, not about hats; Proposition 2.9 shows that hats are exactly what
  the lemma cannot give. Call it the tree lemma.
- The Organisation paragraph (p. 6) omits Appendix B.
- The lines ℓ(a_0, w_0; d) of AS(q) are parametrised by (point, direction), so each line arises from each of its q points;
  say "each line arises q times" (Section 4.2).
- Section 3.6 cites "arXiv:2404.04680 (abstract only)" by number, outside the bibliography, and says it was read only in
  abstract. Either read and cite it properly or drop it.
- References are printed as [AL20], [VM98], [DF84] inside the todos and as numbers in the text; harmless in a draft.
- Section 1: "These are known when Δ−1 is a prime power" should be "These exist when ..." (non-existence for other Δ is
  open).

## Part 5. The table of results

**21. All formula-based numbers recompute.** `tables_ref.py` recomputes 152 numbers: the Moore bounds of Table 1; the
D = 3, 4, 6 values and the regular values of Tables 1 and 9 from Theorems 3.2, 4.8, 4.12, 5.8, 5.18; Delorme's values in
Example 4.4 and Remark 5.9; the 2013 D = 7 values (2r+1)·2N(q) of Table 5; κ(δ) and all nine rows of Table 6; the orders
in Corollaries 6.24–6.26 and Remark 6.27 from the stated set sizes; the Ω_q table of Section 7 and the numbers 1348–208 666
after Theorem 7.5; the closed forms of A and B; every order in Table 8 from the stated group (2|G|), every percentage, the
condition r^l ≡ 1 (mod m) for the four metacyclic groups, and 2|SL(2,83)| = 1 143 408. I found no discrepancy.

**22. The graphs I rebuilt from the paper's text** (Part 8) all have the stated order, degrees and diameter: Table 1 rows
(11,3), (13,3), (15,3), (7,4) 359 and 350, (11,4) 1782, (7,5) 1152, (9,5) 2662, (7,6) 9592 and 9348, the Haar graph
(7,8) 95 760 of Example 8.5, and Table 6 row (7,7) 23 488.

**23. gap — traceability of the computer-dependent rows.** Section 1 promises that every computer-checked statement names
its check. For the nine D = 7 records and the 33 Haar graphs at D = 8–10, Appendix D names directories, and one example file
(`d7D7_hex5_mirror81_n23598.sol`). Give, for every row of Tables 1, 5 and 8 that depends on data, the name of the data file
and of the check (program and log), for example as an extra column of Table 9 or a table in Appendix D.

**24. presentation — Table 1, column "reg.".** The caption says the column gives "the largest regular graph we give, when the
record graph is not regular". The column is empty for the D = 7 rows, which by the caption means that the D = 7 record graphs
are regular. Nothing in Section 6 says so (hubs have degree 2r+1+deg_Y, and Y need not be regular). Say for each row whether
the record graph is regular.

**25. presentation — Table 9.** (i) The status column has six symbols (P, C, L, T, L′, L*); a referee cannot weigh "a graph of
the same order and the same shape is proved in Lean" (L′) or "a Lean proof exists on a branch but has not been re-checked"
(L*). Keep P and C, and describe the Lean coverage once in Appendix C. (ii) "—" at (10,8), (12,8), (14,8), (16,8) is
ambiguous: it can be read as "no value". Give the best value that the paper regards as established for these cells (or say
explicitly that the paper gives none), so that readers can update the table. (iii) Rows "(8,9)–(16,9)" and "(7,10)–(16,10)"
have no values; print them or refer to Table 8 in the caption only.

**26. The 2013 column.** See point 27 (Part 6) for the comparison with the CombinatoricsWiki.

## Part 6. Prior work and credits

Every reference in the bibliography was looked up (zbMATH, Crossref, arXiv, publisher pages), as were the CombinatoricsWiki
page and its revision history. All cited works exist. For [BGS06] and [BPR00] only the abstracts and secondary descriptions
(zbMATH reviews, the Dynamic Cage Survey) were accessible; the points that rest on them say so. The points below are what needs
changing.

**27. The 2013 values are right.** Every 2013 value printed in Tables 1, 5, 8 and 9 and in the text agrees with the
CombinatoricsWiki table (http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs, current revision
of 18 February 2022; the https address fails with a certificate error, so keep http) and with Table 4 of [MS13] (p. 37,
"accessed on 10 March 2013"). The two differ only at (13,3), (15,3) and in the survey's misprint at (11,10), as the paper
says. The sentence in Section 1 that the wiki has changed since 2013 only at (13,3) and (15,3) is right: the only change of
values in the page history is the edit of 30 March 2021 (270 → 274 and 370 → 374, credited to Araujo and López); the edit of
18 February 2022 only added references. The values (6,7) 8310, (8,7) 40 586, (4,8) 2184, (3,9) 506, (4,9) 4970 and
(3,10) 800 quoted in the text also agree.

**28. gap (missing credit) — the bipartite literature behind the table is not cited.**
- C. Delorme, Large bipartite graphs with given degree and diameter, J. Graph Theory 9 (1985), no. 3, 325–334,
  doi:10.1002/jgt.3190090304. (The wiki and [MS13] print volume 8; Crossref has volume 9.)
- J. Bond and C. Delorme, New large bipartite graphs with given degree and diameter, Ars Combin. 25C (1988), 123–132 (it
  tabulates 3 ≤ Δ ≤ 16, 3 ≤ D ≤ 10, the range of the present table).
These are the basic references for the problem the paper is about and must be cited in Section 1. Moreover, the wiki credits
the D = 4 and D = 6 entries improved here (346, 1734, 3064, 4946, 5134; 8992, 142 464, 374 452, 842 048, 884 062) to
"graph duplications found by C. Delorme and G. Farhi", while the paper attributes them to [D85a, §8(a),(b)]. Check which
paper contains these constructions (Delorme's J. Graph Theory paper is the natural candidate) and credit accordingly; this
also bears on point 9 ([DF84], "which we have not seen").

**29. gap (missing credit) — bipartite Moore graphs.** Section 1 credits the characterisation (for D ≥ 3, Δ ≥ 3, attained
only by generalized polygons) to Feit–Higman and [MS13]. Add R. Singleton, On minimal graphs of maximum even girth,
J. Combin. Theory 1 (1966), 306–332, which [MS13] credits for this result together with Feit and Higman.

**30. error (incomplete credit) — Section 6.1: "[ovoids of Q(6,q)] do not exist ... for q prime, q ≥ 5 [BGS06]".** The
result is due to C. M. O'Keefe and J. A. Thas, Ovoids of the quadric Q(2n,q), European J. Combin. 16 (1995), 87–92, who proved
that Q(6,q), q odd, q ≠ 3, has no ovoid as soon as every ovoid of Q(4,q) is an elliptic quadric (and settled q = 5, 7), together
with [BGS06], which proved that hypothesis for every prime q (this is from the zbMATH review of O'Keefe–Thas and the
abstract of [BGS06], which lists the non-existence for Q(6,q), q prime, q > 3, as an application). Cite both. (Example 4.6
cites [BGS06] for the Q(4,p) statement, which is correct.)

**31. gap (credits) — distance-2 ovoids of H(q) (after Proposition 6.4).** The sentence "these are known only for q = 2, 3, 4
[DWVM08], [BI16]" should credit the constructions and the classification: for H(3), A. De Wispelaere and H. Van Maldeghem,
A distance-2-spread of the generalized hexagon H(3), Ann. Comb. 8 (2004), 133–154 (H(3) is self-dual); for H(4), De Wispelaere
and Van Maldeghem, Codes from generalized hexagons, Des. Codes Cryptogr. 37 (2005), 435–448, and [DWVM08]; and the
classification of the distance-2 ovoids of H(2), H(3), H(4) by Pech and Reichard (2009), as cited in [BI16]. [BI16] was
published as A. Bishnoi and F. Ihringer, The non-existence of distance-2 ovoids in H(4)^D, Contrib. Discrete Math. 12 (2017),
157–161; cite the published version. Distinguish H(q) from its dual H(q)^D here (H(2)^D and H(4)^D have none).

**32. presentation — Section 8.4.** The girth-30 statement is right: the Dynamic Cage Survey (DS16, version 3 of 2013) gives
the record (3,30)-graph, of order 1 143 408 = 2|SL(2,83)|, as Exoo–Jajcay's lift of the θ-graph (dipole with three parallel
edges) over SL(2,83), citing [EJ11]. But "[BPR00] use PSL(2,q) × Z_3" is too narrow: according to the same survey their groups
include PSL(2,53) × Z_2, PSL(2,83) × Z_3 and PGL(2,q) × Alt(4). Write "products of PSL(2,q) or PGL(2,q) with small groups".
"Dipole lifts over metacyclic groups are probably behind Loz's values [LS08]": the wiki credits the values marked L (those
beaten at D = 5, 8, 9, 10) to E. Loz within the project of Loz, Pérez-Rosés and Pineda-Villavicencio. Find the publication that
describes these graphs and cite it, instead of "probably".

**33. presentation — recent preprints (Sections 5.7 and 6.10).** R. Rajiv's preprint exists (Zenodo, 30 September 2026,
doi:10.5281/zenodo.23052995, with data and verification files); its abstract claims improvements for general graphs at
(14,3), (15,3), (19,3), (20,3), (13,4), (14,4), (15,4), (17,4), (18,4), (19,4), (11,6), (13,6), (15,6), (16,6). Since Section 6.10
says that "the ideas are the same" as in its Lemma 5 and Theorem 3, the comparison must be precise (what is in the preprint,
what is new here) and should not rest on the label "unrefereed". [Co26] exists (arXiv:2406.18994, v2 of 24 January 2026; a
table for general graphs, with no bipartite table); the "entries of September–October 2026" of the online table need a date of
access and a description of what they contain.

**34. gap (missing credit) — Section 3.6, bipartite graphs of diameter 3.** Besides [FMP13] and [AL20], the papers on bipartite
graphs with small defect are relevant to the upper bounds at D = 3 that the paper quotes (n_b(7,3) = 80): C. Delorme,
L. K. Jørgensen, M. Miller and G. Pineda-Villavicencio, On bipartite graphs of diameter 3 and defect 2, J. Graph Theory 61
(2009), 271–288, and On bipartite graphs of defect 2, European J. Combin. (2009); R. Feria-Purón and G. Pineda-Villavicencio,
On bipartite graphs of defect at most 4, Discrete Appl. Math. 160 (2012), 140–154. The claim "n_b(7,3) = 80, a value known to be
exact [FMP13]" is right: [FMP13] proves that there is no bipartite (7,3,−4)-graph. The credit for 190 at (11,3) to [FMP13] and,
independently, [AL20] matches the wiki.

**35. Bibliography corrections.**
- [BDF82]: pages 23–31, not 23–32 (Crossref, zbMATH).
- [EP16]: the first author is István Estélyi ("I. Estélyi", not "A. Estélyi").
- [FMP13]: Discrete Math. 313 (2013), no. 4, 381–390 (volume issue and pages missing).
- [HMP02]: Discrete Math. 244 (2002), 137–152 (pages missing).
- [BI16]: published version, point 31.
- [CG94]: published in Graph Theory, Combinatorics, and Algorithms, Vol. 1 (Kalamazoo 1992), Wiley 1995, 221–233.
- [AL20]: the journal byline is "Gabriela Araujo, Nacho López" (the todo already notes this); key [AL20] for a 2022 paper is odd.
- [CDPS22]: J. Combin. Des. 31 (2023); the key says 22 (online 2022).
- [DGQ]: I found no trace of publication in zbMATH, Crossref or by web search; the wiki lists it as "submitted". The paper's
  wording ("we found no published version") is right; [MS13] does not cite it.
- [Go86]: the thesis exists (J. Gómez Martí, UPC 1986, advisor M. A. Fiol); since the readings of its figures matter
  (point 7), give the page numbers of Figs. 2.21a/b.

**36. gap — Proposition 4.10 and Remark 4.11 ("very likely known").** [BLP09], [CCEM08] and [FWX19] exist and are about
m-ovoids of W(3,q). The authors should settle whether the 2-ovoids C_a ∪ C_{q−a} are among the known ones (the todo asks the
co-authors) before submission; a paper should not say "very likely known" of its own proposition. If they are known, cite and
shorten (and part (a) follows from [E85] in any case, point 13).

**37. presentation — Section 8.1.** The name "Haar graph": [HMP02] is a fine reference; [EP16] is correctly cited for
general groups. Theorem 8.4 is standard for bi-Cayley graphs; the paper says it claims no novelty, which is right.

## Part 7. What a referee would ask to cut, move or change

**38. Split the paper.** The four parts have different methods and different standards of proof:
(a) D = 3, 4, 6 from polygons (Sections 2–5) and the classical D = 7 bounds (Sections 6.1–6.8, Table 6): fully proved, explicit,
a good paper on its own;
(b) the D = 7 records (Section 6.9, Corollaries 6.24–6.26, Remark 6.27): computer-found data; an appendix or a data note;
(c) Section 7 (Ω_q): a critique of six published table entries; a short separate note, sent to J. Gómez before submission
(the todo already raises this); in the main paper one paragraph and Theorems 7.3 and 7.5 would be enough;
(d) Section 8.3 and Table 8 (33 Haar graphs found by search, no family): a computational note with a data supplement.
If the authors prefer one paper, at least move (b), the relabelling part of (c) (Section 7.4, Lemmas 7.8–7.21, Table 7) and
(d) to appendices or supplements.

**39. Cut.**
- The paragraph after Theorem 8.4 on the "per-side Moore bound" and its strictness for D = 8, 9, 10: it reproves that there
  are no bipartite Moore graphs of these diameters, which is not needed anywhere.
- The optimality claims that depend on an integer-programming solver (Example 4.6: "21 is the maximum for this family";
  Remark 4.9: "AS(5) has no m-ovoid for m = 1, ..., 4"), unless the program and log are named. (I confirmed by exhaustive
  search that AS(3) has no 1-ovoid, hence no 2-ovoid; this part of Remark 4.9 can stay with "by exhaustive search".)
- Corollary 5.15 for q = 2 and Appendix B: no cell depends on it (the paper says so after Corollary 5.15). The q = 2
  whisker set is correct (I checked exactness and the 208-vertex graph), but it adds nothing.
- Corollary 4.13's "in particular n_b(Δ, 4) ≥ 2q^2Δ": it improves no cell; keep it as a remark.
- Remark 3.5 (point 8).

**40. Shorten.** Appendix C (Lean) to one paragraph: what is formalised, where, and how it was checked; the status letters in
Table 9 then become unnecessary. Appendix D: keep the description of the checks and the exceptions to the two-program rule;
move the list of "checks of this paper's text" to the repository.

**41. Rewrite the prior-work subsections (3.6, 4.4, 5.7, 6.10, 8.4).** Sentences like "The literature search behind this
draft did not search for it specifically", "As everywhere in this paper, 'nothing found' means only that the searches we made
returned nothing", "In the sources we searched we found nothing on ..." describe the authors' process, not the literature. A
journal paper should state what is known, with citations, and what is new. Where the authors suspect a result is known
(Proposition 4.10, Proposition 6.4, Remark 6.13), they should find out (the todos ask the co-authors) or say "we could not find
it in the literature" once.

**42. Say how the explicit ingredients were found, and disclose the AI use.** The first todo says the draft "keeps search and
AI out of the mathematics and mentions computation only as computer-checked". For the reader this hides useful information:
the mirrored sets, friendly sets, hub graphs, the (7,4) list and all Haar connection sets were found by computer search, and
readers who want to extend the tables need to know how. One paragraph on the search methods belongs in the paper. Most
journals now also require a statement on the use of AI tools; given how the work was produced (the first todo), a clear
statement is needed.

**43. Remove the todo list and the "Points for the co-authors" page before submission**, and the internal history
(references to "the 20 October meeting", "the lab notes", "the referee of the diameter-7 note"), which a journal reader cannot
follow.

## Part 8. What I recomputed (scripts in `research/referee/joint-paper-checks/`)

All scripts were written from the paper's text. `apsp64.c` is a bit-parallel all-pairs breadth-first search (checks simple,
bipartite, connected, maximum degree, exact diameter). Results (full output in `run.log`):

- **Section 3** (`hat4_ref.py`, `hat4_free.py`): S(q; a, c) from (C1)–(C6) equals Table 2 row by row for q = 4, 5, 7, 8, 9 (all
  admissible (a, c)) and q = 11, 13 (three (a, c) each); 2(q^2+q+6) vertices; G and R have diameter 3; R is (q+2)-regular.
  Without the rotation, or without the link H_1 I K_0, the diameter is 4 (all q tested). The coordinate-free version works for
  every choice of four points of ℓ at q = 3, 4, 5 (at q = 3 the structure is 5-regular on 36 vertices).
- **Section 4.2** (`as_ref.py`): AS(q) as printed is a GQ of order (q−1, q+1) for q = 3, 5, 7, 9 (counts, and the GQ axiom on a
  sample); every line meets the two quadrics in exactly 2 points, for every κ_1 with κ_1κ_2 = 1/(4ε); the quadrics meet only
  in x and e; the graph of Corollary 4.8 is (q+2)-regular of diameter 4 with 90, 350, 882, 1782 vertices. AS(3) has no 1-ovoid
  (exhaustive search).
- **Section 4.3** (`singer_ref.py`, q = 3, 5, 7): Proposition 4.10(a),(b); exactly the pairs {a, q−a} give 2-ovoids; the spread
  {yK} is totally isotropic; the general claim of Remark 4.11 (δ_0) holds in all 24 + 90 + 224 cases tried; Corollary 4.12 and
  its regular completion: 120, 416, 1000 vertices, diameter 4, (q+3)-regular.
- **Appendix A** (`app359_ref.py`): as in point 22 and Part 3.
- **H(q)** (`hexagon.py`, `hex_basic.py`): for q = 2, 3, 4, 5, Tits' equations as printed give a generalized hexagon (each
  point on q+1 lines, N lines, incidence graph of diameter 6 and order equal to the Moore bound); the lines through e_0 are as
  stated; Lemma 2.4(c) holds; the SL(3) maps of Fact 2.3 are collineations. For q = 7, 8 the same builder was used in the
  Section 5 runs (counts checked, doubled graphs of diameter 6).
- **Section 5** (`d6_ref.py`, `d6_even.py`, `jz_sym.py`, `jz_conj.py`, `thmR_ref.py`): Lemma 5.1 (a)–(e) for every z (q = 3, 5, 7)
  and Lemma 5.10 (q = 2, 4, 8); the table of (c, c_0, c_1) for q = 3, ..., 13 (−c a non-square, G zero-free); ν constant on the
  lines of S \ {v}; W is an exact whisker set with q^2(q^2−1) lines (q = 3, 5, 7; q = 4, 8 for the even rule; q = 2 for the
  12 lines of Appendix B); Lemma 5.6(c) and the key identities 5.7 and 5.13; the doublings of Theorem 5.3 (built from
  Definition 2.5 directly): 1020 and 1386 (q = 3, m = 2, 3), 9592 (q = 5), 45 428 (q = 7), 208 (q = 2), 3524 (q = 4),
  85 180 (q = 8) vertices, all of diameter 6 and maximum degree q+m; Theorem 5.18 with a completion found by the swap
  argument of Lemma 5.17: 968, 1224 (q = 3, m = 2, 3) and 9348 (q = 5), regular of diameter 6. The structural proof of point 3.
- **Section 6** (`d7_ref.py`): Lemma 6.2(a) for q = 4, 5; Corollary 6.20 built from the printed recipe (Σ_0, the Hermitian
  spread, σ from Proposition 6.17 with random choices, the pendant hub graph of Lemma 6.19): q = 4, 8204 vertices, and q = 5,
  23 488 vertices, maximum degree q+2, diameter 7; breaking (H3) at one point of R (negative control) gives diameter 8.
- **Section 7** (`d8_lemmas.py`, `perp_ref.py`, `omega_ref.py`): Lemma 7.10 on H(3) and H(4); Lemma 7.13 for every block
  pattern with 3 ≤ α ≤ 8; Fact 7.14 (point 17); Lemma 7.17(a) on random triples in Q(6,3) and Q(6,5); Lemma 7.20 (point 10);
  Ω_2 (1890 vertices) and Ω_3 (14 560 vertices) with the thesis labelling: diameter 9 in both readings with both block types,
  10 with one block type, as stated after Corollary 7.6.
- **Section 8** (`haar_ref.py`): the two D = 5 connection sets give diameter 5 (1152 and 2662 vertices); Example 8.5 gives
  diameter 8 on 95 760 vertices, and α permutes S as stated (g has order 3).
- **Tables** (`tables_ref.py`): point 21.

Not rechecked: the record graphs whose ingredients are only in data files (D = 7 records, Haar graphs of Table 8 other than
Example 8.5), the Lean proofs, and the integer-programming claims.
