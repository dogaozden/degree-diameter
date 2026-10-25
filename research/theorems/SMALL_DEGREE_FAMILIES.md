# Formulas behind the small-degree records (thm-smallfamilies, 2026-10-24/25)

Job "thm-smallfamilies" (Opus), two sessions: branch `claude/small-degree-families-g7zllq` (Oct 24, cut off by the
usage limit) and its continuation `claude/thm-smallfamilies-formulas-49l6io` (Oct 25). Scripts and outputs are in
`smallfam/`, and every claim below names its script and saved output.
- "Table" means research/frontier/TABLE.md. The wiki page has not changed in these cells since January 2012
  (research/lifts/LITERATURE.md §1, voltage-lifts branch).
- "Haar graph" H(G,S): (g,A) ~ (s·g, B) for s ∈ S, with |S| = Δ and 2|G| vertices.
- "Exhaustive" means every connection set (or voltage assignment) up to isomorphism was tested (§2.2).
- "Screened" means a short simulated-annealing run per group (hanneal / lanneal). A screen finds solutions where they
  exist (calibrated on every known record group, §6.1) but it is **not** a proof that none exists.

## Short answer

1. **New record (4,7) = 864** (table 840, Bond–Delorme), from the first session.
   - There are exactly three 4-regular Haar graphs of diameter 7 on 864 vertices, one for each of three groups of
     order 432.
   - The main one is H(Heis(F_9) ⋊ C16, S), with an explicit formula (§1). It is on master.
   - Nothing larger was found. This session screened Haar graphs of all groups of order 448–500, and Δ = 4 lifts of
     the 2+2 bases over all groups of order 217–260 (§6).
2. **Three of Loz's records have closed forms, and each is the unique Haar graph with its parameters** (§2.1):
   - (3,9) 506 = Cay(AGL(1,23), {x ↦ 5x, x ↦ 14x, x ↦ −x+1});
   - (4,8) 2184 = H((C7 ⋊ C3) × Dic13, S);
   - (4,9) 4970 = H(Z71 ⋊ Z35, {1, y, x·y¹³, x⁹·y¹⁹}).
3. **Which (p, k, r) can solve: a theorem** (§2.3). For G = Z_p ⋊_r Z_k with o = ord(r), every walk of H(G, S)
   is the image of a walk in a universal group Z[ζ_o]^(Δ−2) ⋊ Z_k that does not depend on p.
   - Counting the walk values in each fibre gives a rigorous bound N = pk ≤ B(k, o), valid for every S.
   - At Δ = 3, D = 7–10 it excludes 1,524 of the 1,639 metacyclic groups ever scanned, and no solving group.
   - In particular it excludes 658 of the 666 groups whose multiplier group has index > 6. That was the first
     session's main empirical pattern; it is now mostly a theorem.
   - Among the 115 groups the bound leaves open, 21 solve, and the solve rate falls steadily with N/B (§3.2).
   - At Δ = 4 the same bound shows that no Z_p ⋊ Z_k with k ∈ {2, 3, 4, 6} can reach the (4,8) or (4,9) table
     sizes, for any p.
4. **No bounded-order family covers a row** (§2.4).
   - For fixed action order o, metacyclic Haar graphs have N ≤ (2D+1)^((o+1)(Δ−1)): polynomial in D.
   - The records grow like (Δ−1)^D, so any metacyclic family that holds a whole row needs an action order that grows
     with D.
   - This is an asymptotic statement only. At D ≤ 10 the crude bound is useless, and the fibre bound of item 3 does
     the work.
   - The record groups do: o = 11, 35, 32 at (3,9), (4,9), (4,10).
5. **Complete negatives, new this session** (§2.5):
   - **(3,7):** no cubic bipartite graph with more than 168 vertices and diameter 7 has a colour-preserving group of
     automorphisms acting freely with at most 8 vertex orbits. All Haar graphs and all lifts of the 2+2, 3+3 and
     4+4 bases were searched exhaustively up to the Moore bound.
   - **(4,8):** all 3,924 groups of order 1093–1200 except order 1152 were screened. The eleven groups that came within
     cost 5 (all affine-type, like Loz's group) are exhaustively negative; the closest is cost 1.
   - **(4,9):** the closest group found is C101 : C25 = SmallGroup(2525,3) (5,050 vertices), 2 vertices short and
     exhaustively negative. The library screen of orders 2486–2700 found nothing.
   - **(3,10):** no group of order 401–600 (except 512 and 576) gives a cubic Haar graph of diameter 10. The
     closest is SmallGroup(486,40) at cost 2. K3,3 lifted over C17 : C8 (816 vertices) is exhaustively negative
     (cost 4).
   - **(3,7), (3,9), (3,10):** no Z_p ⋊ Z_k cubic Haar graph beats the table. Every group up to the Moore bound
     was scanned, and the family maxima are 140, 234, 506 and 660 vertices at D = 7–10.
6. **No new record in (3,7), (3,9), (3,10), (4,8) or (4,9).** Most near misses in every cell are affine-type
   groups: an abelian normal subgroup F_q (or a product of two) with a cyclic or metacyclic group acting by
   multiplication (§3.1, §5). The exceptions are SmallGroup(486,40) at (3,10), a 3-group extended by C2, and
   SmallGroup(432,243) at (4,7).

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
- The coordinator re-checked it all-pairs and recorded it on Oct 24 (research/RESULTS.md).

*The two other graphs* (`graphs/d4D7_n864_others.txt`; apsp VALID). Both are vertex-transitive (|Aut| = 864):
- SmallGroup(432,247) = (C3 × C3) : (C2 . S4), girth 6;
- SmallGroup(432,249) = (C2 × C2) : ((C9 : C3) : C4), girth 10.

The three graphs are pairwise non-isomorphic. In each group all plan solutions form a single isomorphism class:
144, 24 and 24 plan solutions respectively (`isoclasses.py` → `runs/d4D7_sg432_isoclasses.txt`).

*How it was found.* `allgroups.py 4 7 …` runs over every SmallGroup of each order:
- a rank test;
- the abelianization bound of §2.2;
- a GAP export of the multiplication table and an Aut(G)-reduced plan;
- an exhaustive test of every remaining set with `hx`.

At order 432 all 775 groups were handled: 572 searched, 182 failing the rank test, 21 the bound. The exhaustive run
is complete for orders 421–447 and 449–467. Orders 448 and 468 are partial (500 of 1,396 and 48 of 55 groups);
this session screened all of 448–500 (§6.2). Above 432 the closest exhaustive results are cost 1 (one vertex short), at three groups of order 440
(880 vertices): C11 : C40, D8 × (C11 : C5) and C11 : (C5 × Q8). SmallGroup(432,243) is also at cost 1.

*Is the exhaustive search itself right?* Four checks:
- **Against igraph.** `hx_check.py` recomputes with igraph the exact diameter of every set on two plan lines of
  SmallGroup(432,233), with the quotient filter on: 858 sets, 2 solutions, 0 mismatches
  (`runs/hx_check_igraph.txt`).
- **Against an independent annealer** (`hx_vs_hanneal.py` → `runs/hx_vs_hanneal_d4D7.txt`).
  - In SmallGroup(432,30) and (432,31), where hx finds nothing, hanneal plateaus at costs 4 and 8 after 1.5 million
    evaluations.
  - In (432,247) and (432,249) it finds solutions in 360–1,366 evaluations.
- **Known records.** At order 420 the same pipeline re-finds Bond–Delorme's group C7 × A5 (8 plan solutions;
  `runs/allgroups_d4D7_420.tsv`).
- **apsp.** Every solution reported anywhere in this file was also checked by apsp.

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
  all of G (GAP; `allgroups.py`, `named.py`). For lifts, the first free voltage runs over Aut(G)-orbit
  representatives *including the identity* (see the bug note in §2.5) and the others over all of G (`lx.c`).
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
- **Lifts and free actions.** A connected bipartite graph X whose colour-preserving automorphism group contains a
  subgroup G acting freely on vertices is a regular G-lift of the multigraph X/G. No element can swap the ends of an
  edge, so G also acts freely on edges and X/G has no loops. So "a lift of some base with b vertices" is the same as
  "a free colour-preserving action with b orbits".

### 2.3 Which (p, k, r) can solve: the cyclotomic fibre bound (new)

Setting: G = Z_p ⋊_r Z_k, p prime, o = ord_p(r) ≥ 2 (so o | k and o | p − 1). Normal form as in §2.2:
S = {(0,0), (0, j1), (1, j2), (a3, j3), …} with o ∤ j1.

**The universal group.** Let ζ = ζ_o and U = Z[ζ]^(Δ−2) ⋊ Z_k, with product (P; J)(Q; L) = (P + ζ^J Q; J + L). Its
generators are u_0 = e, u_1 = (0; j1) and u_i = (ε_{i−2}; j_i) for i ≥ 2 (ε_f is the f-th unit vector).
- r is a primitive o-th root of unity in F_p, so Φ_o(r) = 0 and ζ ↦ r is a ring map Z[ζ] → F_p.
- Hence φ(P; J) = (P_0(r) + Σ_{f≥1} P_f(r)·a_{f+2}, J) is a group homomorphism U → G with φ(u_i) = s_i.
- Every walk of H(G, S) from (e, A) or (e, B) is the image of the walk with the same generator sequence in the
  infinite graph H(U, {u_i}). So φ maps each ball of H(U) onto the ball of the same radius in H(G, S).

The walk values ending at J therefore form a finite set W_J ⊂ Z[ζ]^(Δ−2) that depends on (k, o, j, D) but **not on
p, r or a3, a4, …**. H(G, S) has diameter ≤ D exactly when each W_J (from both start sides, on both target sides)
maps onto F_p.

**Theorem (fibre bound).** If H(Z_p ⋊_r Z_k, S) is connected with diameter ≤ D, then p ≤ min_J |W_J| for its
pattern j. So N = pk ≤ B(k, o) := k · max over admissible j of min_J |W_J|.
- *Proof:* φ maps W_J onto the p vertices (a, J), a ∈ F_p, of the target side.
- "Admissible" means two things:
  - o ∤ j1: s1 is an element whose j-part acts non-trivially. Such an element exists in every connected H(G, S),
    and §2.2 conjugates it to (0, j1).
  - gcd(j1, j2, …, k) = 1: otherwise S does not generate G and the graph is disconnected.
- j is taken up to multiplication by units u of Z_k. That is the Galois action ζ ↦ ζ^u, which does not change
  |W_J|. ∎

**Computation** (`cyclobound.py --fiber`, numpy, exact arithmetic in the power basis of Z[ζ_o]). It was applied to
all 1,639 groups of the first session's exhaustive Δ = 3 scans (`runs/frob_d3D{7..10}.txt`, every Z_p ⋊ Z_k in the
scanned ranges). Outputs: `runs/cyclofiber_d3D{7,8,9,10}.txt`, summary `runs/cyclofiber_summary.txt`.

| index c = (p−1)/o | groups | solving | excluded by the bound | left open | solving among open |
|---|---|---|---|---|---|
| 1 | 344 | 8 | 315 | 29 | 28 % |
| 2 | 262 | 9 | 223 | 39 | 23 % |
| 3–6 | 367 | 4 | 328 | 39 | 10 % |
| > 6 | 666 | 0 | **658** | 8 | 0 % |
| all | 1,639 | 21 | **1,524** | 115 | 18 % |

- No solving group is excluded. This is a soundness check of the proof and the code; `cyclosummary.py` asserts it.
- A direct check (`cyclocheck.py` → `runs/cyclocheck.txt`) uses a BFS in the actual group G, written independently.
  Its universal-group side reuses `cyclobound.zeta_powers`. For 50 random (group, S) pairs (Δ = 3 at D = 7 and 9,
  Δ = 4 at D = 6), the number of distinct ball elements in every fibre J never exceeds |W_J|: 0 violations.
- Squad referee r3-c3 (`research/squads/r3-smallfam/c3/`) checked the proof and the code line by line. It also
  verified on 7 groups that φ maps the U-balls exactly onto the G-balls, per side and per fibre. No error found.
- The first session's conjecture "index > 6 never solves" (0 of 666) is now a theorem for 658 of those groups. The
  other 8 fail by exhaustive search.
- The bound excludes these groups one by one, for their actual (k, o, p); it does not prove "index ≤ 6" in general.
  - Since p = c·o + 1 ≤ B(k, o)/k, the largest index it allows over k ≤ 40 is 5, 8, 10 and 17 at D = 7, 8, 9, 10
    (`cycloindex.py` → `runs/cycloindex.txt`).
  - The largest index among actual solutions is 2, 4, 4 and 6.
  - At D = 7 the bound does give a clean statement: every cubic Haar graph of a Z_p ⋊ Z_k with k ≤ 40 and
    diameter 7 has index ≤ 5.
- The simpler version without fibres (`cyclobound.py`, `runs/cyclobound_d3D*.txt`) excludes 1,335 groups, 644 of
  them with index > 6.
- Tightness: Loz's Z23 ⋊ Z11 has N = 253 against B(11, 11) = 451. Over k ≤ 40, the largest N the bound allows is
  497 at D = 9 and 812 at D = 10. The true family maxima are N = 253 and 330. So the bound overshoots by a factor
  of about 2, as a counting bound must: it ignores collisions under the reduction mod p.
- Bound tables for every k ≤ 40 and o | k (`cyclotable.py --fiber`, `runs/cyclotable_fiber_d3D{9,10}.txt`). At
  D = 9, beating 506 requires N ≥ 254, and for k ≤ 40 only seven (k, o) allow it; the largest allowed is Z71 ⋊ Z7
  (N ≤ 497).
- The same argument works for F_q ⋊ C_k (r ∈ F_q^*), since ζ ↦ r is still a ring map.
- For squarefree m, replace Z[ζ_o] by Z[x]/(product of the distinct Φ_{o_i}), where o_i is the order of r mod the
  i-th prime factor of m. Two conditions are needed:
  - m squarefree, because Φ_o(r) ≡ 0 holds mod p but not always mod p²;
  - the normal form, i.e. some s1 with 1 − r^{j1} a unit mod m and an a2 that is a unit.

  If r ≡ 1 mod some prime of m, the normal form can fail (squad referee r3-c3: m = 15, r = 7). Then use the
  construction of §2.4 with a formal a-part for every non-identity element. Loz's (4,8) S, used in §5, is already
  in normal form: 1 − r and a2 = 1 are units mod 91.

How the bound and the truth scale with D (Δ = 3; N = |G|, half the vertex count):

| D | Moore limit on N | largest N the fibre bound allows (k ≤ 40) | true maximum over Z_p ⋊ Z_k | table / 2 |
|---|---|---|---|---|
| 7 | 127 | 84 (Z7 ⋊ Z12) | 70 | 84 |
| 8 | 255 | 203 (Z29 ⋊ Z7) | 117 | 128 (ours: 144) |
| 9 | 511 | 497 (Z71 ⋊ Z7) | 253 (Loz) | 253 |
| 10 | 1023 | 812 (Z29 ⋊ Z28) | 330 | 400 |

The bound grows with D about as fast as the Moore limit, while the true maximum falls behind from D = 10 on. At
D = 7, for k ≤ 40, the bound alone rules out a metacyclic Haar graph above the table.

**Δ = 4** (`cyclotable4.py` → `runs/cyclotable4_d4D{8,9}.txt`, k ≤ 10, fibre version):
- At (4,8), which needs N ≥ 1093, every Z_p ⋊ Z_k with k ∈ {2, 3, 4, 6} has N ≤ 1,014, for any p.
- At (4,9), which needs N ≥ 2486, the same k are capped at 1,686. So are (k, o) = (8, 2), (8, 4), (9, 3) and
  (10, 2), at most 2,286.
- These are exactly the cases with φ(o) ≤ 2: each formal a-part then lives in a lattice of rank ≤ 2.
- Larger φ(o) allows much more: (5, 5) allows 5,885 and (7, 7) 8,323 at D = 9. So small k is not excluded as such,
  only small rank.

**Corollary (complete for this family).** No Haar graph of any Z_p ⋊_r Z_k (p prime) beats the table at
D = 7, 9 or 10. At D = 8 the family stays at 234 against 256.
- Every group with N up to the Moore limit (127, 255, 510, 1023) was scanned exhaustively
  (`runs/frob_d3D{7,8,9,10}.txt`; `frobcover.py` confirms that every (p, k, r) is present).
- The family maxima are 140, 234, 506 and 660 vertices.

### 2.4 No bounded-order metacyclic family covers a row (new)

Take G = Z_m ⋊_r Z_k for any m, with o = ord_m(r).
- Use the universal group (Z[x]/(xᵒ − 1))^(Δ−1) ⋊ Z^(Δ−1). There is no normal form here, so all Δ − 1 non-identity
  elements s_i = (a_i, j_i) get formal a-parts, and the j-part is replaced by the signed generator counts
  n ∈ Z^(Δ−1).
  - The basis vector e_i of Z^(Δ−1) acts by multiplication by x^(j_i), so (P; n)(Q; n′) = (P + x^(⟨n, j⟩) Q; n + n′).
  - φ(P; n) = (Σ_i P_i(r)·a_i, ⟨n, j⟩ mod k) is a homomorphism onto the subgroup generated by S (it needs rᵒ = 1),
    and φ(ε_i; e_i) = s_i.
  - The squad referee r3-c4 tested this on 2,000 random words: 0 failures.
- A walk of length ≤ D has |n|₁ ≤ D. Each formal a-part is a sum of at most D terms ±xᵉ, so its o coefficients lie
  in [−D, D].
- Hence N ≤ (2D+1)^(Δ−1) · (2D+1)^(o(Δ−1)) = (2D+1)^((o+1)(Δ−1)).

For fixed o this is polynomial in D, while the Moore bound and the records grow like (Δ−1)^D. A metacyclic family
whose action order stays bounded can therefore hold only finitely many cells of a row.

This crude bound is purely asymptotic. At Δ = 3, D = 10 it is about 194,000 even for o = 1, far above the Moore
limit of 1,023, so it constrains nothing at D ≤ 10. The fibre bound of §2.3 is the one that bites in the table's
range. A family that holds a whole row
needs o → ∞, at a rate of at least about D log(Δ−1) / ((Δ−1) log(2D+1)). This is the standard growth argument for
virtually abelian groups (Z_m × ⟨yᵒ⟩ is abelian of index o), made explicit.

*Prior work.* I did not find the fibre bound of §2.3 in the sources I could check, but I could not read them all.
- Dougherty and Faber (arXiv:math/9412223) treat abelian Cayley graphs.
- Macbeth, Šiagiová and Širáň, Discrete Math. 312 (2012) 94–99, "offer a result for Cayley graphs of metacyclic
  groups for general degree and diameter". I could read only the abstract (the repository returned HTTP 403), so
  its form is unknown to me.
- Squad card r3-c1 (`research/squads/r3-smallfam/c1/notes.md`) searched further: no matching upper bound in any
  source it could read, and the 2012 paper was refused by every copy it tried.
- Treat the growth corollary as known in spirit, and the fibre bound as new here unless that paper contains it.

What the records show:
- The record groups do use large action orders: o = 11 at (3,9), 35 at (4,9), 32 at (4,10).
- The Δ = 4 records use a different group type at each D (§3.1). So a row-covering family, if one exists, cannot be
  a fixed-o metacyclic one; it would have to let o grow with D as Loz's groups do.

### 2.5 Complete negatives (all groups, GAP SmallGroups, nothing skipped unless stated)

Coverage of every run below was re-checked against NrSmallGroups (`completeness.py` → `runs/completeness_resume.txt`).

- **(3,7): every base with at most 8 vertices.** Haar graphs (2 vertices), 2+2 lifts (4), lifts of all three 3+3
  bases (6) and lifts of all six 4+4 bases (8) were searched exhaustively over every group giving 168 < n ≤ 254
  vertices (254 is the Moore bound):
  - Haar, orders 85–127 (`runs/allgroups_d3D7.tsv`): closest (96,65) and (96,66), 4 vertices short;
  - 2+2, orders 43–63 (`runs/lift_b22_D7.tsv`): best cost 16. At order 42 (`runs/lift_b22_D7_order42.tsv`),
    Conder's group C2 × (C7:C3) is the only one of the 6 groups with solutions (24 in the plan);
  - 3+3 bases b33_0 and b33_1, orders 29–42 (`runs/lift_b33_{0,1}_D7.tsv`), and K3,3, orders 29–42
    (`runs/lift_b33_2_D7_idfix.tsv`, 100 groups, best cost 6);
  - all six 4+4 bases b44_0 … b44_5, orders 22–31 (`runs/lift_b44_{0..5}_D7.tsv`): all 37 groups for each base, no
    rigorous filter used, best costs 8, 24, 16, 8, 8, 8.
    - The cube b44_5 is the one base here whose first free edge is not parallel to a tree edge; it was run with the
      fixed plan that includes the identity.

  By §2.2 this proves: **no cubic bipartite graph with more than 168 vertices and diameter 7 has a colour-preserving
  group of automorphisms acting freely with at most 8 vertex orbits.**
  - A free colour-preserving action has equally many orbits on the two colour classes, so the quotient is an m+m
    base with m ≤ 4. The lists of such bases are complete (`basegen.py`: 1, 1, 3 and 6 classes for m = 1–4).
  - Conder's graph has 4 such orbits. Squad referee r3-c4 checked the logic, the base lists and the order ranges.
- **(3,9), Haar:** every group of every order 254–319 (`runs/allgroups_d3D9.tsv`), all 56,092 groups of order 256
  included: no diameter-9 graph. **No cubic Haar graph with 508–638 vertices has diameter 9.** At order 320, 34 of
  1,640 groups were done.
  - Closest: C17 : C16 (N = 272), 4 vertices short; then C3 × ((C2 × C2) : (C3 : C8)) and C3 × (Q8 : (C3 : C4))
    (288) and C2 × (C31 : C5) (310), each 9 short.
  - At odd D, hx reports N + (uncovered) when the first BFS already fails. The first session's coverage summary
    sorted these raw values, so its "best costs" at D = 7 and 9 were misleading; they are recomputed here.
- **(3,10), Haar:** every group of every order 401–600 except 512 and 576 (`runs/allgroups_d3D10.tsv`; 400 is
  partial, 126 of 221). No diameter-10 graph. **No cubic Haar graph with 802–1,200 vertices has diameter 10, except
  possibly for groups of order 512 or 576.**
  - Closest: SmallGroup(486,40) = (C3 . ((C9 × C3) : C3)) : C2, at cost 2 (972 vertices). Also cost 4 at
    C29 : C14 and C2 × (C29 : C7) (406), at (432,243) and at C11 : C40 (440).
  - Orders 521–600 (1,438 groups, 583 searched): the closest is only cost 12, (C5 × C5) : SL(2,3) (600), so the
    near misses get worse beyond 520.
- **(3,10), lifts near 816:** K3,3 over SmallGroup(136,3) = C17 : C8 (squad card c2's lead). 17,608,192
  assignments plus the identity pass of 2,515,456: no solution, best cost 4
  (`runs/d3D10_k33_sg136_3_exhaustive.txt`, `_identity.txt`).
  - The voltage-lifts session reports another 3+3 base (their b3_3_0) over Z17 ⋊ Z8 as exhaustively negative at
    cost 2. Our b33_0 reaches the same cost 2 there by annealing (squad card c1), so it is probably the same base.
- **2+2 lifts at (3,8), (3,9), (3,10):** all groups of orders 73–113, 127 and 129–170, and 201–239
  (`runs/lift_b22_D*.tsv`): none.
  - Partial: order 114 (4 of 6), 128 (189 of 2,328) and 240 (43 of 208).
  - The best are cost 8 (order 80), 12 (order 140), and 2 (Z29 ⋊ Z7 at 812 and C4 × (C11 : C5) at 880).
  - For (3,9) the Moore bound allows 2+2 lifts up to order 255, so (3,9) is not closed.
  - (3,10), all 67 groups of order 243 = 3⁵ (972 vertices; the shape of the Haar near miss (486,40)): 55 searched
    exhaustively, 12 removed by the rigorous filters, no solution, best cost 8 (`runs/lift_b22_D10.tsv`).
- **(4,8): the best groups of the full screen** (§6.2), all eleven at cost ≤ 5, are exhaustively negative (`onegroup.py`,
  `runs/d4D8_sg*_exhaustive.txt`):

| group | structure | sets tested | best cost |
|---|---|---|---|
| (1100,27) | C11 : (C5 × (C5 : C4)) | 2,096,367 | **1** |
| (1100,26) | (C5 : C4) × (C11 : C5) | 2,379,393 | 3 |
| (1120,1078) | ((C2 × C2 × C2) : C7) × (C5 : C4) | 1,505,716 | 3 |
| (1100,18) | C11 : (C5 × (C5 : C4)) | 2,438,631 | 4 |
| (1134,167) | C7 : (C3 × (C9 : C6)) | 3,815,994 | 4 |
| (1134,176) | C7 : (((C9 × C3) : C3) : C2) | 1,242,969 | 4 |
| (1200,485) | (C5 × C5) : (C3 : C16) | 1,242,486 | 4 |
| (1134,40) | C7 : (((C3 × C3 × C3) : C3) : C2) | 1,911,390 | 5 |
| (1140,15) | C5 : (C19 : C12) | 978,957 | 5 |
| (1197,7) | C7 : (C19 : C9) | 693,714 | 5 |
| (1240,7) | C31 : (C5 × Q8), centre C2 | 1,475,741 | 2 |

- **Bug found and fixed this session** (by squad card c6). In lift mode `allgroups.py` left the identity out of
  the plan for the first free voltage.
  - That is harmless when the first free edge is parallel to a tree edge, since parallel edges need distinct
    voltages. That holds for b22, b33_0, b33_1 and every b44 except the cube.
  - It is wrong for K3,3 (b33_2), the cube (b44_5), b55_13, b55_14 and the 6+6 bases.
  - Of the earlier claims, only K3,3 at (3,7) was affected. It was redone in full above. Every run in this file uses
    the fixed code or an unaffected base.

### 2.6 Exhaustive maxima of the affine family F_q ⋊ C_k

| family | D = 7 | D = 8 | D = 9 | D = 10 |
|---|---|---|---|---|
| Δ=3, Z_p ⋊ Z_k (p prime) | 140 | 234 | **506** | 660 |
| Δ=3, F_q ⋊ C_k (q = p^e, e ≥ 2) | – | – | – | 702 (F_27 ⋊ C13) |
| Δ=4, Z_p ⋊ Z_k with k ≤ p, N above the table | none (best cost 2: Z31 ⋊ Z15, Z37 ⋊ Z12) | none for N = 1093–1870 (best 8) | squares groups p = 79, 83 fail | – |
| Δ=4, F_q ⋊ C_k | 800 (F_25 ⋊ C16) | none for N = 1093–1700 (best cost 4: F_49 ⋊ C24, N = 1176) | none for N = 2486–2688 (partial; best 44 uncovered) | – |

Files: `runs/frob_d3D*.txt`, `runs/affq_d3D*.txt`, `runs/frob_d4D7.txt`, `runs/frob_d4D8.txt`,
`runs/affq_d4D7.txt`, `runs/affq_d4D8.txt`, `runs/affq_d4D9.txt`, `runs/d4D9_squares_p79_p83.txt`.
- The Δ = 3 rows are complete up to the Moore bound (§2.3 corollary; `frobcover.py` checks that every (p, k, r) is
  present).
- The Δ = 4 rows are not complete. `frob_scan.py` now restricts to k ≤ p, so groups with a large central part were
  never scanned at Δ = 4: 809 of the 1,179 Z_p ⋊ Z_k with N = 1093–1870 are missing from `runs/frob_d4D8.txt`.
  - Below N = 1200 they are covered by the all-groups screen (§6.2).
  - Above that, the Loz-like ones are screened in §6.2 (`lozlike.py`).
  - The rest have small action order.

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

In every affine case the walk sums are signed sums of powers of one field element (§2.3 makes this exact).
- This session adds the near misses. Almost every group that came within cost 5 of a record, in any cell, is of
  the same type:
  - the ten (4,8) groups of §2.5;
  - the cost-1 groups of order 440 at (4,7): C11 : C40, D8 × (C11 : C5), C11 : (C5 × Q8);
  - C29 : C14 and C2 × (C29 : C7) at (3,10);
  - C17 : C8 on the 3+3 bases and Z29 ⋊ Z7 on the 2+2 base at (3,10).

  There are two exceptions: SmallGroup(486,40), a 3-group extended by C2 and the closest group at (3,10), and
  SmallGroup(432,243), a near miss at both (3,10) and (4,7).
- Exhaustive searches of this family show it does not reach beyond the table in the other cells (§2.6).

### 3.2 Solve probability falls with N / B(k, o)

Among the 115 Δ = 3 metacyclic groups that the fibre bound of §2.3 leaves open (`cycloratio.py`,
`runs/cyclofiber_summary.txt`):

| N/B | [0, 0.5) | [0.5, 0.6) | [0.6, 0.7) | [0.7, 0.8) | [0.8, 0.9) | [0.9, 1) |
|---|---|---|---|---|---|---|
| open groups | 4 | 9 | 13 | 19 | 17 | 53 |
| solving | 3 | 4 | 4 | 3 | 1 | 6 |

As a predictor over all scanned groups, N/B beats N alone at every D (AUC 0.976, 0.991, 0.999, 0.998 at D = 7–10,
against 0.940, 0.953, 0.922, 0.983 for N; `cycloauc.py`). So the answer to "which (m, k, r) solve" for Δ = 3 is:
- compute B(k, ord r), which is cheap;
- a group with N > B cannot solve;
- one with N/B ≲ 0.6 solves about half the time;
- one with N/B ≳ 0.8 rarely does.

The conjecture is that the same holds for Δ = 4 and 5. The Δ = 4 bound is computable (`cyclotable4.py`) but costs
about k³ patterns, so it was tabulated only for k ≤ 10 (§2.3). Where the records are, its ratio N/B_j lies in a
narrow band (§5).

### 3.3 In the small cells, success is decided by the far lower tail, so search all groups

`structure_factor.py` → `runs/structure_factor.txt` measures the uncovered count of random S in the record groups
and in control groups of the same order that have no solution.

| group | μ = N e^{−W/N} (per condition) | mean of random S | variance/mean | 1st percentile | valid fraction |
|---|---|---|---|---|---|
| (3,9) Z23 ⋊ Z11 (record) | 67 | 1.03 μ | 111 | 0 | 4.8 % of normal forms |
| (4,7) (432,233) (record) | 69 | 2.5 μ | 163 | 8 | 3.3·10⁻⁴ of normal forms |
| (4,7) (432,249) (record) | 69 | 3.8 μ | 217 | 20 | – |
| (4,8) (1092,4) (record) | 54 | 6.1 μ | 237 | 11 | 1.3·10⁻⁵ of plan sets |
| (4,7) controls (432,30), (432,3), (444,1) (no solution) | 69–76 | 3.1–4.1 μ | 120–166 | 14–38 | 0 |

- The Poisson model of SIZE_LAW.md predicts variance/mean 1 and P(valid) = e^{−μ} ≈ 10^{−24}–10^{−30}. Neither
  holds here.
- Every group, solving or not, is strongly overdispersed. The record groups differ from the controls only in the
  extreme lower tail.
- So in the small-N cells no averaged quantity can tell which group will solve. That covers μ, the screening score
  and the quotient balance of §4; for the metacyclic groups the bound of §2.3 is the exception.
- **That is why exhaustive coverage of all groups of the right order found (4,7).** This session applied the same
  recipe to (4,8) (all groups of order 1093–1300 except 1152, 1280, 1296), (4,7) (448–500), (4,9) (library orders
  2486–2700 except 2624) and (3,10) (exhaustive to order 600). It found near misses but no record.

## 4. The metacyclic records of the voltage-lifts session (45 solutions, D ≥ 7)

- `meta.py` re-checks all 47 saved metacyclic solutions with its own BFS; all are VALID
  (`runs/meta_parse_check.txt`).
- **Fibre balance** (`fibers.py` → `runs/fibers_out.txt`).
  - At the quotient Z_k, and at Z_d ⋊ Z_k for each prime d | m, the records are a little better balanced than
    random S in the same group: percentile 0.0–0.6, and μ_d/μ_unif ≤ 1.13 at d = 1.
  - For large k, many random S already fail the rigorous bound (42 % at Z97 ⋊ Z64).
- **Which runs solve** (`predict.py`, `predict_test.py` → `runs/predict_out.txt`, `runs/predict_test_out.txt`;
  188 anneal runs in the four cells with both outcomes). The two quotient features do not separate solved from
  stalled runs (within-cell permutation p = 0.995 and 0.83). μ = N e^{−W/N}, i.e. N, does (p < 10⁻⁴). Within one
  cell these runs differ mainly in N, so this agrees with §3.2: the group-level quantity that matters is the bound
  B(k, o), not quotient balance.

## 5. Weak patterns

- **Near misses are Frobenius products and extensions.** At (4,8) the ten closest groups (§2.5) are products of
  two Frobenius-type groups or extensions of C7 or C11 by them, the shape of Loz's (C7 ⋊ C3) × Dic13. The
  "record-shaped" products screened directly (`frobprod.py`) did no better:
  - at (4,8), orders 1201–1400 (66 products): best cost 9;
  - at (4,9), orders 2486–2800 (50 products, all in orders missing from the SmallGroups library): best cost 10.
- **Within a group, which S solves is arithmetic, not counting** (`jfibre.py` → `runs/jfibre_d3.txt`).
  - In each solving Δ = 3 group, compare the fibre count F(j) = min_J |W_J| of the solving patterns with that of all
    admissible patterns.
  - When p is small (p ≤ 13) the solutions sit at the patterns of largest F.
  - When p is larger they do not. In Loz's Z23 ⋊ Z11, 90 of the 110 patterns pass F ≥ p, and the 6 solutions have
    F = 40 against a maximum of 41. In Z43 ⋊ Z7 the solutions spread over the top 71 %.
  - So |W_J| decides which groups can solve, while which S solves depends on collisions under reduction mod the
    prime 𝔭.
- **The Δ = 4 records sit in a narrow band of N/B_j.** B_j = k · min_J |W_J| is the fibre bound at the record's
  own j-pattern (`recordbound.py`, `recordbound_sqf.py` → `runs/recordbound_d4.txt`).
  - Loz's (4,8) Z91 ⋊₅₁ Z12 has N/B_j = 0.379. Its modulus is composite but squarefree, so the ring is
    Z[x]/(Φ₂Φ₃), of rank 3, because r has order 2 mod 13 and 3 mod 7.
  - Loz's (4,9) Z71 ⋊ Z35 has 0.267, and our (4,10) Z97 ⋊ Z64 has 0.269.
  - Loz's (3,9) Z23 ⋊ Z11 has 0.575, because the Δ = 3 bound is tighter: there is only one free a-part.
  - If the Δ = 4 band holds, a group needs B_j/N of roughly 2.5–4 for some pattern. Three data points are only
    suggestive.
  - The band is at most a necessary condition. The (4,9) near miss C101 : C25 (exhaustively negative, 2 short) sits
    at N/B_j = 0.377 at its best pattern, inside the band.
- **A central involution.** The record groups of even order mostly have centre exactly C2 or containing one:
  - Conder's (3,7), our (3,8), all three (4,7) groups, Loz's (4,8), our (4,10) and (5,8);
  - but not PGL(2,5) × Z13 at (5,7) (centre Z13), nor our (5,10) group.
  - The faithful version of the (4,8) group (SmallGroup(1092,28), trivial centre) fails.
  Such a graph is a 2-fold cover of the Haar graph of G/⟨z⟩.
- **Arithmetic progressions.** The Δ = 3 j-patterns are sometimes arithmetic progressions with the translation on
  the middle element ((3,9): {0, 1, 6} in Z11). This is not a rule (`jpat.py`).
- **AGL(1,p) Cayley graphs.** Cay(AGL(1,p), {x ↦ gx, x ↦ g⁻¹x, x ↦ −x+1}) for p ≡ 3 (mod 4) gives diameters
  6, 7, 9, 9, 11 for p = 7, 11, 19, 23, 31 (`runs/agl_cayley.txt`). Only p = 23 is a record, so this is not a
  row family.

## 6. Dead ends and searches with no record

### 6.1 Cost conventions and screen calibration

Costs: 0 always means a graph of diameter ≤ D.
- **hanneal** (all Haar screens) reports the number of uncovered vertices. At odd D it is the sum over the two start
  sides.
- **hx** (exhaustive Haar) reports the same at even D. At odd D it returns N + (uncovered) when the first BFS already
  fails, and skips the second; the near-miss counts quoted in §1 and §2.5 subtract N.
- **lanneal** and **lx** (lifts) count far (source, target) pairs, with one source per base vertex. lx multiplies an
  early-stopped first source by the number of base vertices.

Why a screen is meaningful:

- hanneal re-finds every known solving group in seconds: Loz's (4,8) group in 1.7k–3k evaluations, the (4,7) groups
  in 360–1,366, Conder's (3,7) lift (lanneal) in under 3 s.
- The (4,9) record group is harder. Loz's Z71 ⋊ Z35 needs 47k–79k evaluations, 8–13 s
  (`runs/hanneal_calibration_d4D9_2485.txt`), and a 5 s screen there reached only cost 2. So (4,9) screens need
  15 s or more per group.
- `fscreen.py` and `flscreen.py` re-find Loz's (4,8) group and Conder's lift in their test runs.

### 6.2 This session

| cell | search | coverage | result |
|---|---|---|---|
| (4,8) | Haar, every SmallGroup, 3 s anneal (`fscreen.py`) | orders 1093–1200 except 1152: 3,924 groups, of which 2,813 annealed, 861 fail the rank test and 250 the abelianization bound | no solution; the 10 best are exhaustively negative (§2.5) |
| (4,8) | Haar, every SmallGroup, 3 s anneal (`fscreen.py`, tags `_1201`, `_1236`, `_1248`, `_1251`) | orders 1201–1300 except 1280 and 1296: 1201–1235 (1,945 groups, 1,114 annealed), 1236–1250 without 1248 (169), 1248 (RESULT_1248), 1251–1300 (474, 320 annealed) | no solution; best cost 2 at C31 : (C5 × Q8) = SmallGroup(1240,7), exhaustively negative (§2.5); otherwise ≥ 8 |
| (4,8) | Frobenius products A × B (`frobprod.py`), index ≤ 6, central part ≤ 3 | orders 1201–1400, 66 groups | best cost 9 (S3 × (C29 : C7), 1218) |
| (4,9) | Frobenius products, index ≤ 6, central part ≤ 2, 15 s | orders 2486–2800, 50 groups (orders missing from the library) | best cost 10 (D5 × (C23 : C11), 2530) |
| (4,9) | Haar, every SmallGroup, 5 s anneal, then 2 × 30 s for cost ≤ 10 (`fscreen.py`, `fscreen2.py`) | orders 2486–2700 in the library: 1,029 groups (589 annealed, 161 rank > 3, 279 abelianization bound). Not covered: order 2624 (1,672 groups, C41 by 2-groups) and the 61 orders the library lacks | no solution; best cost 2 after stage 2 at C101 : C25 = SmallGroup(2525,3) (5,050 vertices), exhaustively negative: the normal form (§2.2) has 1,513,200 sets, no solution, best 2 short (`z101.py` → `runs/d4D9_z101x25_exhaustive.txt`) |
| (4,7) | Haar, every SmallGroup, 2 s anneal | orders 449–500: all 1,936 groups, 1,365 annealed; order 448: all 1,396 groups, 758 annealed | no solution; best cost 4 at C2 × (C19 : C12) (456) and C13 : C36 (468), both exhaustively negative (2 and 1 vertices short; `runs/d4D7_sg*_exhaustive.txt`) |
| (4,7) | lifts of the 4-regular 2+2 base ((2,2),(2,2)), 3 s (`flscreen.py`) | orders 217–260 except 256, 693 groups | best cost 8 (orders 220, 224); 216 (= 864) reaches 6 |
| (3,10) | Haar, exhaustive | orders 453–520 except 512 (2,218 groups) | none; best cost 2, SmallGroup(486,40) |
| (3,10) | 2+2 lifts, exhaustive | all 67 groups of order 243 | none; best cost 8 |
| (4,9) | Loz-like Z_p ⋊ Z_k (index ≤ 3, central part ≤ 3, action order ≥ 10; `lozlike.py`, 2 × 30 s; calibration re-finds Loz's group) | N = 2486–3000, 7 groups | best cost 6 (Z37 ⋊ Z72, N = 2664) |
| (4,8) | Loz-like, 2 × 10 s | N = 1093–1870, 20 groups (most have k > p, missed by the first session's frob scan) | best cost 8 (Z43 ⋊ Z28) |
| (4,7) | Loz-like, 2 × 5 s | N = 433–1093, 23 groups | best cost 4 (C13 : C36, exhaustively negative), then 6 |
| (3,10) | squad r2: 3+3 bases, orders 134–145; 4+4 bases, 101–106 | ~150 groups | best cost 2 (b33_0 over C17 : C8, re-anneal), 4 (K3,3 over C17 : C8, then exhaustive) |
| (3,9) | squad r2: 3+3 and 4+4 bases, orders 64–100 | ~180 groups | best cost 32 |
| (3,7) | squad r2: cube, orders 22–26 (exhaustive, with the identity pass); 5+5 bases, 17–25 (226 of 510 pairs) | – | best cost 8 (cube, exhaustive), 16 (b55_1 over C17) |
| (3,7) | squad r2 wildcard: 2-switch annealing of general cubic bipartite graphs, 170 vertices | – | best 92 (46 pairs at distance 8) |
| (3,7) | lifts of all six 4+4 bases, exhaustive (`allgroups.py --base`, fixed plan) | orders 22–31, all 37 groups per base | none; best cost 8 (proves the 8-orbit theorem of §2.5) |

The voltage-lifts session had also screened 1,538 Haar groups at (4,9) for N = 2,486–2,580 (best cost 10) and rich
lifts at (4,8) for 2,186–2,208 vertices (none).

### 6.3 Earlier (first session)

| idea | test | result |
|---|---|---|
| squares groups Z_p ⋊ Z_{(p−1)/2} above Loz at (4,9) | `hx`, p = 79, 83 | 18 and 40 uncovered, exhaustive |
| prime-m metacyclic Haar at (4,7) above 840 | `frob_scan.py`, N = 421–1093 | none; best cost 2 |
| F_q ⋊ C_k Haar at (4,7) and (4,8) | `affq.py` | maximum 800 at (4,7); none at (4,8) (best 4) |
| the three order-432 groups at (3,10) (864 > 800) | `named.py` | best costs 6–18 |
| AGL(3,2) at (4,8) | `named.py` | best cost 43 |
| central-involution metacyclic groups at (4,8) | `named.py` (`runs/centralinv_d4D8.log`) | Dic5 × (C11 : C5) best 6 (the run was cut off) |
| squad r1 (8 Haiku cards; `research/squads/r1-smallfam/`) | Heisenberg 5^{1+2}, 7^{1+2}; affine F_q^n ⋊ H; PSL × C_n; small-abelianization SmallGroups 1093–1140; composite-m metacyclic; perfect-ish groups at (4,9); Δ = 4 lifts of 2+2 bases | none; best costs 6 (Z77 ⋊ Z15), 9, 14, 22 |
| group-level quotient balance as a predictor of solved runs | `predict_test.py` | p = 0.83–0.995 |

## 7. Tools in `smallfam/`

| file | what |
|---|---|
| `hx.c` | Exhaustive Haar search over a plan of (s1, s2) pairs, with the remaining elements free, for metacyclic groups or any multiplication table. Includes the quotient filter (QMAP / QFILTER). Validated against igraph (`hx_check.py`). |
| `lx.c` | Exhaustive voltage-lift search over a small base, for a table group or a metacyclic group; first free voltage from a plan. |
| `hanneal.c`, `lanneal.c` | Simulated annealing for Haar graphs and for lifts, over any table group, with targeted moves. |
| `abfilt.c`, `liftbound.py` | Rigorous abelianization bound and generic lattice bound (§2.2). |
| `allgroups.py` | Every SmallGroup of each order: filters, GAP export (table, Aut(G)-reduced plan, abelianization map), then hx or lx. Resumable. Lift-mode plans include the identity (fixed this session). |
| `onegroup.py`, `onelift.py` | The same for one SmallGroup (Haar or lift; `--identity-only` completes an old run). |
| `fscreen.py`, `fscreen2.py`, `flscreen.py`, `gtab.c` | Fast all-groups screens: one GAP process per batch exports only generator permutations, `gtab` rebuilds the table in C, and a worker pool anneals. About 1 group/s at N = 1100. `fscreen2.py` re-anneals the low-cost groups. |
| `frobprod.py` | Products of two Frobenius-type groups F_q ⋊ C_a (faithful or not), tables built in numpy, for orders the library lacks. |
| `cyclobound.py`, `cyclotable.py`, `cyclotable4.py`, `cyclosummary.py`, `cycloratio.py`, `cycloauc.py`, `cycloindex.py`, `jfibre.py`, `metabound.py` | The bounds of §2.3–2.4 and their evaluation. |
| `cyclocheck.py`, `recordbound.py`, `recordbound_sqf.py` | Independent check of the bound against BFS in real groups; the bound at a record's own pattern (prime and squarefree moduli). |
| `lozlike.py`, `frobcover.py` | Loz-like metacyclic candidates (small index and central part) screened directly; coverage check of a metacyclic scan against every (p, k, r). |
| `basegen.py`, `bases/` | All connected cubic bipartite bases with 3+3, 4+4 and 5+5 vertices (3, 6 and 15 multigraphs) and the five simple 6+6 graphs. |
| `lift_edges.py`, `verify/apsp` | Edge list of a lift for the independent all-pairs check (Conder's graph re-built and VALID). |
| `screen.py`, `lscreen.py`, `metascreen.py`, `named.py`, `named_edges.py`, `frob_scan.py`, `affq.py`, `squares.py`, `heis.py`, `heisq.py`, `meta.py`, `fibers.py`, `predict.py`, `predict_test.py`, `canon.py`, `isoclasses.py`, `autgroup.py`, `agl_cayley.py`, `jpat.py`, `summarize.py`, `completeness.py`, `structure_factor.py` | First-session tools (see that session's notes in git history). |

GAP 4.12 with the SmallGroups library (`gap-smallgrp` **and `gap-smallgrp-extra`**) was installed from Ubuntu
packages in the container. Without the extra package, orders such as 1092 and 1096–1140 are missing. Orders above
2000 are only partly covered: in 2486–2700, 154 orders (2,701 groups) are available and 61 are not.
