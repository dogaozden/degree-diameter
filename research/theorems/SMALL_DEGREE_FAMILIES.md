# Formulas behind the small-degree records (thm-smallfamilies, 2026-10-24)

Job "thm-smallfamilies" (Opus). Branch `claude/small-degree-families-g7zllq`. Scripts and outputs are in
`smallfam/`, and every claim below names its script and saved output.
- "Table" means research/frontier/TABLE.md. The wiki page has not changed in these cells since January 2012
  (research/lifts/LITERATURE.md §1, voltage-lifts branch).
- "Haar graph" H(G,S): (g,A) ~ (s·g, B) for s ∈ S, with |S| = Δ and 2|G| vertices.
- "Exhaustive" means every connection set up to isomorphism was tested (§2.2).

## Short answer

1. **New record (4,7) = 864** (table 840, Bond–Delorme). Exactly three 4-regular Haar graphs of diameter 7 on 864
   vertices exist, one for each of three groups of order 432. The main one is H(Heis(F_9) ⋊ C16, S) with an explicit
   formula (§1).
2. **Three of Loz's records have closed forms, and each is the unique Haar graph with its parameters:**
   - (3,9) 506 = Cay(AGL(1,23), {x ↦ 5x, x ↦ 14x, x ↦ −x+1});
   - (4,8) 2184 = H((C7 ⋊ C3) × Dic13, S);
   - (4,9) 4970 = H(Z71 ⋊ Z35, {1, y, x·y¹³, x⁹·y¹⁹}).
   "Unique" is checked over every group of the order (§2.1).
3. **What the record groups have in common.** All of them are, or contain with index 2, a group N ⋊ C_k: an abelian
   or Heisenberg normal subgroup N, with a cyclic group acting by field multiplication. The graph is then a lift of a
   circulant or 2+2 base whose voltages turn with the rotation (§2.2).
   - Our metacyclic records of the voltage-lifts session have the same group type, but their S is random-like.
   - Which of those groups solved is predicted by N alone. Quotient balance does not predict it (permutation test
     p = 0.83 and 0.995, against p < 10⁻⁴ for μ; §4).
4. **No family covers a row.** The Δ = 4 records use a different group type at each diameter:
   - D = 5: a cyclic lift of a 3+3 base;
   - D = 7: Heis(F_9) ⋊ C16;
   - D = 8: (C7 ⋊ C3) × Dic13;
   - D = 9: Z71 ⋊ Z35;
   - D = 10: Z97 ⋊ Z64.
   Within the affine family the exhaustive maxima stay at or below the table (§2.4).
5. **Complete negatives.**
   - No cubic Haar graph with more than 168 vertices has diameter 7, and no 2+2 cubic lift does either.
   - No group of order 254–319 gives a cubic Haar graph of diameter 9 (all 56,092 groups of order 256 included).
   - No group of order 401–431 gives one of diameter 10.
   - At (4,8) and (4,9) about 200 structured groups were tested, by me and an 8-Haiku squad; none works (§6).

---

## 1. Records

### 1.1 (4,7): 864 vertices (table 840)

*Construction.* F_9 = F_3[i]/(i²+1), v = a + b i, ω(v, w) = ab′ − ba′.
- Heis(F_9) = {(v, z) : v ∈ F_9, z ∈ F_3}, (v, z)(w, z′) = (v + w, z + z′ + 2ω(v, w)): the extraspecial group 3^{1+2}
  of exponent 3.
- λ = 1 + i has order 8 and norm λ⁴ = −1, so φ(v, z) = (λv, −z) is an automorphism of order 8.
- G = Heis(F_9) ⋊ ⟨y⟩ with y of order 16 acting by φ, so y⁸ is central. G = SmallGroup(432,233).
- **S = {1, y, x·c·y¹⁴, c²·y⁶}**, where x = (1, 0) is a translation and c = (0, 1) generates the centre of
  Heis(F_9). In coordinates (v, z, j) this is S = {(0,0,0), (0,0,1), (1,1,14), (0,2,6)}.
  - This is the simplest of the 136 normal-form solutions (`runs/d4D7_heis_normalform.txt`).
  - It gives the same graph as the published S = {(0,0,0), (2i,0,9), (2+i,0,8), (1+2i,2,14)}: igraph isomorphism,
    apsp VALID (`verify/d4D7_n864_normalform_check.txt`).

*Checks.* 4-regular, bipartite, diameter 7, girth 8, |Aut| = 432 (only the translations of G).
- `smallfam/graphs/build_d4D7_n864.py`: pure Python, no GAP, BFS from all 864 vertices
  (`verify/d4D7_n864_build.txt`).
- The coordinator's apsp.c (all pairs, no symmetry) is VALID on this edge list and on an edge list built
  independently from GAP's arithmetic in SmallGroup(432,233) (`verify/d4D7_n864_apsp.txt`).
- igraph agrees.
- Edge list `graphs/d4D7_n864_heis9xC16.edges.gz`, sha256 (uncompressed)
  73231da4081f762588e5d5270bc2ae911807e1f3b204ff5ff79fad4d6779de25.

*The two other graphs* (`graphs/d4D7_n864_others.txt`; apsp VALID). Both are vertex-transitive (|Aut| = 864):
- SmallGroup(432,247) = (C3 × C3) : (C2 . S4), girth 6;
- SmallGroup(432,249) = (C2 × C2) : ((C9 : C3) : C4), girth 10.

The three graphs are pairwise non-isomorphic. In each group all plan solutions form a single isomorphism class:
144, 24 and 24 plan solutions respectively (`isoclasses.py` → `runs/d4D7_sg432_isoclasses.txt`).

*How it was found.* `allgroups.py 4 7 421 546` runs over every SmallGroup of each order:
- a rank test;
- the abelianization bound of §2.2;
- a GAP export of the multiplication table and an Aut(G)-reduced plan;
- an exhaustive test of every remaining set with `hx`.

At order 432 all 775 groups were handled: 572 searched, 182 failing the rank test, 21 the bound. Orders 421–448
are done so far (`runs/allgroups_d4D7.tsv`); the run continues to 546 and skips order 512 (10,494,213 groups).

*Is the exhaustive search itself right?* `hx_check.py` recomputes with igraph the exact diameter of every set on
two plan lines of SmallGroup(432,233), with the quotient filter on: 858 sets, 2 solutions, 0 mismatches
(`runs/hx_check_igraph.txt`). Every solution reported anywhere in this file was also checked by apsp.

Two remarks:
- The 840 record is not a ceiling. The size law (SIZE_LAW.md §3.3) predicted 876 [788–980] for a good Haar
  group at (4,7).
- The groups were simply never tried. Annealing (`hanneal.c`) finds an S in Heis(F_9) ⋊ C16 within 200–1,500
  evaluations, i.e. seconds.

## 2. Proved (by proof, or by exhaustive computation as stated)

### 2.1 Loz's records rebuilt, with closed forms and uniqueness

| cell | group | S (normal form) | graphs | girth, \|Aut\| | files |
|---|---|---|---|---|---|
| (3,9) 506 | Z23 ⋊_2 Z11 | {1, y, x·y⁶} | **1** (both groups of order 253 searched) | 14, 506 (vertex-transitive) | `runs/d3D9_z23x11_exhaustive.txt`, `canon_d3D9_z23x11.txt`, `aut_d3D9_506.txt` |
| (4,8) 2184 | SmallGroup(1092,4) = (C7 ⋊ C3) × Dic13 = Z91 ⋊ Z12, r of order 6 | first SOL in `runs/d4D8_sg1092_4_allsols.txt` | **1** (all 77 groups of order 1092 handled) | 10, 2184 (vertex-transitive) | `runs/allgroups_d4D8_1092.tsv`, `d4D8_sg1092_4_isoclasses.txt` |
| (4,9) 4970 | Z71 ⋊_2 Z35 | {1, y, x·y¹³, x⁹·y¹⁹} | **1** (all 4 groups of order 2485 searched) | 12, 2485 | `runs/d4D9_z71x35_normalform.txt`, `canon_d4D9_z71x35.txt`, `d4D9_order2485_others.txt` |

- **(3,9) as a Cayley graph.** Cay(AGL(1,23), {x ↦ 5x, x ↦ 14x, x ↦ −x+1}). 5 is the least primitive root mod 23
  and 14 = 5⁻¹. The other primitive roots give diameter 10 or 11 (`agl_cayley.py`, `runs/agl_cayley_23_roots.txt`).
- **(4,8): the faithful product fails.** The other "(C7:C3) × (C13:C4)", SmallGroup(1092,28), has C4 acting
  faithfully on C13. It has no solution (best cost 4). PSL(2,13), the obvious guess for 2184 = 2·1092, has best
  cost 8.
- **(4,9): the other groups of order 2485.** These are (Z71 ⋊ Z5) × Z7 and (Z71 ⋊ Z7) × Z5, with 6 and 2
  uncovered; Z2485 fails the lattice bound. The list is complete: Z71 is normal and the quotient is Z35.
- If Loz's graphs are Haar graphs, as his search method suggests, these are therefore his graphs.

### 2.2 General facts used throughout

- **Normal form** (`frob_scan.py`, `affq.py`). Take G = F_q ⋊ C_k with C_k acting by multiplication by r, faithful
  or not. Every connected H(G, S) is isomorphic to one with S = {(0,0), (0, j1), (1, j2), s3, …}, where r^{j1} ≠ 1.
  *Proof:*
  - H(G,S) ≅ H(G, xSy) ≅ H(G, σS) for x, y ∈ G and σ ∈ Aut G, so assume (0,0) ∈ S.
  - Some element has a j-part acting non-trivially, else S lies in the abelian subgroup F_q × ker and the graph is
    disconnected. Conjugating by the translation (c, 0) maps (a, j) to (a + c(1 − r^j), j), which kills its
    a-part.
  - Some element has a ≠ 0, else S ⊂ C_k. Scaling a ↦ ua is an automorphism; use it to set that a-part to 1. ∎

  So the search space has (k−1)·k·N^{Δ−3} sets, only k² for Δ = 3. For general groups the plan instead takes
  s1 over Aut(G)-orbit representatives, s2 over Stab(s1)-orbit representatives, and the remaining elements over
  all of G (GAP; `allgroups.py`, `named.py`).
- **Cover structure.** For G = K ⋊ ⟨y⟩ with K normal and y of order k, H(G, S) is a regular K-lift of the
  circulant H(Z_k, S̄), where S̄ is the multiset of j-parts.
  - The edge from (j, A) labelled s = κ_s·y^{j_s} carries the voltage φ^{−(j+j_s)}(κ_s), φ being conjugation by y.
  - Proof: right multiplication by K is free with quotient H(Z_k, S̄); take y^j as fibre representatives.
  - So these Haar graphs are exactly the K-lifts of circulants whose voltages turn by an automorphism when the base
    rotates. For K = F_q (Loz), and for K = Heis(F_9) (the 864 graph).
- **Quotient bound** (`hx.c` QMAP filter, `abfilt.c`, `liftbound.py`). Walks of H(G, S) project to H(G/K, S̄).
  Each target vertex within distance D−1 is the end of its geodesic, a non-backtracking walk. So every K-coset on
  the target side needs at least |K| such walks.
  - With K = G′ this is a fast test per group and per image S̄.
  - For abelian G it gives the **generic lattice bound**: |G| is at most the number of walk endpoints in
    Z^{Δ−1}, which is 61 at (3,9), 147 at (4,7) and 309 at (4,9).
  - For lifts of a base with c independent cycles it gives |B|·|G^ab| ≤ the walk endpoints in the Z^c-lift. For
    the 2+2 cubic base that means |G^ab| ≤ 79, 112, 152 at D = 8, 9, 10.
  - The filter never removed a known solution.

### 2.3 Complete negatives (all groups, GAP SmallGroups, nothing skipped unless stated)

- **(3,7), Haar:** orders 85–127, every group (`runs/allgroups_d3D7.tsv`). The best is cost 100.
  **No cubic Haar graph with more than 168 vertices has diameter 7** (2N ≤ 254 by Moore).
- **(3,7), 2+2 lifts:** orders 43–63, every group (`runs/lift_b22_D7.tsv`). The best is cost 16. Order 42 has
  exactly one solving group, C2 × (C7:C3), which is Conder's graph. **Conder's 168 is the largest 2+2 cubic lift of
  diameter 7.**
- **(3,9), Haar:** every group of every order 254–319 (`runs/allgroups_d3D9.tsv`, completeness in
  `runs/completeness.txt`), all 56,092 groups of order 256 included: no diameter-9 graph. **No cubic Haar graph
  with 508–638 vertices has diameter 9.** Orders 320–330 are running.
- **(3,10), Haar:** orders 401–431 (`runs/allgroups_d3D10.tsv`): none. The best is cost 4, at C29 : C14 and
  C2 × (C29 : C7) (N = 406). Orders 432–460 are running.
- **(3,8), (3,9), (3,10), 2+2 lifts:** orders 73–114, 127–168 and 201–224 so far (`runs/lift_b22_D*.tsv`): none.
  The best are cost 8 (order 80), 12 (order 140) and 2 (Z29 ⋊ Z7, the known near miss at 812).

### 2.4 Exhaustive maxima of the affine family F_q ⋊ C_k

| family | D = 7 | D = 8 | D = 9 | D = 10 |
|---|---|---|---|---|
| Δ=3, Z_p ⋊ Z_k (p prime) | 140 | 234 | **506** | 660 |
| Δ=3, F_q ⋊ C_k (q = p^e, e ≥ 2) | – | – | – | 702 (F_27 ⋊ C13) |
| Δ=4, Z_p ⋊ Z_k, N above the table | none (best cost 2: Z31 ⋊ Z15, Z37 ⋊ Z12) | none for N = 1093–1870 (best 8) | squares groups p = 79, 83 fail | – |
| Δ=4, F_q ⋊ C_k | 800 (F_25 ⋊ C16) | none for N = 1093–1700 (best cost 4: F_49 ⋊ C24, N = 1176) | none for N = 2486–2688 (partial; best 44 uncovered) | – |

Files: `runs/frob_d3D*.txt`, `runs/affq_d3D*.txt`, `runs/frob_d4D7.txt`, `runs/frob_d4D8.txt`,
`runs/affq_d4D7.txt`, `runs/affq_d4D8.txt`, `runs/affq_d4D9.txt`, `runs/d4D9_squares_p79_p83.txt`.

## 3. Conjectured, with strong evidence

### 3.1 Records come from affine-type groups over tiny bases

| cell | record | base | group (normal subgroup ⋊ cyclic) |
|---|---|---|---|
| (3,7) | 168 (Conder) | 2+2 | (F_7 ⋊ C_3) × C_2 |
| (3,8) | 288 (ours) | 2+2 | F_9 ⋊ C_8, acting with order 4 |
| (3,9) | 506 (Loz) | dipole | F_23 ⋊ C_11, the index-2 subgroup of AGL(1,23) |
| (4,7) | **864 (new)** | dipole | Heis(F_9) ⋊ C_16, and two others of order 432 |
| (4,8) | 2184 (Loz) | dipole | (F_7 ⋊ C_3) × Dic13 = Z91 ⋊ Z12 |
| (4,9) | 4970 (Loz) | dipole | F_71 ⋊ C_35 |
| (4,10) | 12,416 (ours) | dipole | F_97 ⋊ C_64, acting with order 32 |
| (4,7) | 840 (Bond–Delorme) | dipole | A5 × Z7: the exception |

In every affine case the walk sums are signed sums of powers of one field element, and they spread over the fibres
much better than random words do. At (3,9), random S would leave about 34 vertices uncovered (μ = N e^{−W/N}),
yet 5 % of all normal-form sets work. The evidence is the eight cells above. Exhaustive searches of this family show
it does not reach beyond the table in the other cells (§2.4).

## 4. The metacyclic records of the voltage-lifts session (45 solutions, D ≥ 7)

- `meta.py` re-checks all 47 saved metacyclic solutions with its own BFS; all are VALID
  (`runs/meta_parse_check.txt`).
- **Fibre balance** (`fibers.py` → `runs/fibers_out.txt`).
  - At the quotient Z_k, and at Z_d ⋊ Z_k for each prime d | m, the records are a little better balanced than
    random S in the same group: percentile 0.0–0.6, and μ_d/μ_unif ≤ 1.13 at d = 1.
  - For large k, many random S already fail the rigorous bound (42 % at Z97 ⋊ Z64).
- **Which runs solve** (`predict.py`, `predict_test.py` → `runs/predict_out.txt`, `runs/predict_test_out.txt`;
  188 anneal runs in the four cells with both outcomes). The two quotient features do not separate solved from
  stalled runs (within-cell permutation p = 0.995 and 0.83). μ = N e^{−W/N}, i.e. N, does (p < 10⁻⁴). So "which
  (m, k, r) solve" is decided by N and the seed; we found no group invariant that matters. This agrees with
  REGULARITIES.md and SIZE_LAW.md.

## 5. Weak patterns

- **A central involution.** The record groups of even order mostly have centre exactly C2 or containing one:
  - Conder's (3,7), our (3,8), all three (4,7) groups, Loz's (4,8), our (4,10) and (5,8);
  - but not PGL(2,5) × Z13 at (5,7) (centre Z13), nor our (5,10) group.
  - The faithful version of the (4,8) group (SmallGroup(1092,28), trivial centre) fails.
  Such a graph is a 2-fold cover of the Haar graph of G/⟨z⟩. We used this to pick (4,8) candidates; none worked
  (§6).
- **Arithmetic progressions.** The Δ = 3 j-patterns are sometimes arithmetic progressions with the translation on
  the middle element ((3,9): {0, 1, 6} in Z11). This is not a rule (`jpat.py`).
- **AGL(1,p) Cayley graphs.** Cay(AGL(1,p), {x ↦ gx, x ↦ g⁻¹x, x ↦ −x+1}) for p ≡ 3 (mod 4) gives diameters
  6, 7, 9, 9, 11 for p = 7, 11, 19, 23, 31 (`runs/agl_cayley.txt`). Only p = 23 is a record, so this is not a
  row family.

## 6. Dead ends

| idea | test | result |
|---|---|---|
| squares groups Z_p ⋊ Z_{(p−1)/2} above Loz at (4,9) | `hx`, p = 79, 83 | 18 and 40 uncovered, exhaustive |
| prime-m metacyclic Haar at (4,7) above 840 | `frob_scan.py`, N = 421–1093 | none; best cost 2 |
| F_q ⋊ C_k Haar at (4,7) and (4,8) | `affq.py` | maximum 800 at (4,7); none at (4,8) (best 4) |
| the three order-432 groups at (3,10) (864 > 800) | `named.py` | best costs 6–18 |
| AGL(3,2) at (4,8) | `named.py` | best cost 43 |
| central-involution metacyclic groups at (4,8) | `named.py` (`runs/centralinv_d4D8.log`) | running |
| squad r1 (8 Haiku cards; `research/squads/r1-smallfam/`) | Heisenberg 5^{1+2}, 7^{1+2}; affine F_q^n ⋊ H; PSL × C_n; small-abelianization SmallGroups 1093–1140; composite-m metacyclic; perfect-ish groups at (4,9); Δ = 4 lifts of 2+2 bases | none; best costs 6 (Z77 ⋊ Z15), 9, 14, 22 |
| group-level quotient balance as a predictor of solved runs | `predict_test.py` | p = 0.83–0.995 |

## 7. Tools in `smallfam/` (all new this session)

| file | what |
|---|---|
| `hx.c` | Exhaustive Haar search over a plan of (s1, s2) pairs, with the remaining elements free, for metacyclic groups or any multiplication table. Includes the quotient filter (QMAP / QFILTER). Validated against igraph (`hx_check.py`). |
| `lx.c` | Exhaustive voltage-lift search over a small base, for a table group or a metacyclic group; first free voltage from a plan. |
| `hanneal.c` | Simulated annealing for Haar graphs over any table group, with targeted moves. It reproduces hx's exhaustive optima: Z137 ⋊ Z8 cost 8, Z61 ⋊ Z18 cost 45, … (`runs/screen_d4D8.tsv` against `runs/frob_d4D8.txt`). |
| `abfilt.c`, `liftbound.py` | Rigorous abelianization bound and generic lattice bound (§2.2). |
| `allgroups.py` | Every SmallGroup of each order: filters, GAP export (table, Aut(G)-reduced plan, abelianization map), then hx or lx. Resumable; skips orders with too many groups. |
| `screen.py` | The same group list, but with a short anneal instead of exhaustive search (fast triage). |
| `named.py`, `named_edges.py` | Exhaustive Haar search for groups given as GAP expressions (`Aff(n,q,H)`, `Meta(m,k,r)`, direct products, …), and the edge-list rebuild for apsp. |
| `frob_scan.py`, `affq.py`, `squares.py` | The F_q ⋊ C_k families in normal form (q prime, q a prime power, the squares groups). |
| `heis.py`, `heisq.py` | Explicit models of Heis(F_{p²}) ⋊ C_k; `graphs/build_d4D7_n864.py` is the standalone builder of the record. |
| `meta.py`, `fibers.py`, `predict.py`, `predict_test.py` | Parsing and re-checking the metacyclic records; fibre balance; the solved/stalled test. |
| `canon.py`, `isoclasses.py`, `autgroup.py`, `agl_cayley.py`, `jpat.py` | Canonical forms of S, isomorphism classes (BLISS), automorphism groups, the AGL Cayley description, j-patterns. |
| `summarize.py`, `completeness.py` | Coverage tables of the all-groups runs; per-order completeness against NrSmallGroups (`runs/coverage_summary.md`, `runs/completeness.txt`). |

GAP 4.12 with the SmallGroups library (`gap-smallgrp` **and `gap-smallgrp-extra`**, without which orders such as
1092 and 1096–1140 are missing) was installed from Ubuntu packages in the container.
