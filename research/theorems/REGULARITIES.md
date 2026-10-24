# Regularities in our records, and what they give (theorem-search, 2026-10-24)

Job "theorem-search" (Opus). Branch `claude/theorem-search-regularities-nt0d98`. Every claim below has a script in
this folder and a saved output (named in the item). "Table" means the DS14v2 bipartite table (research/frontier/TABLE.md,
2013); the live CombinatoricsWiki page still returns 503/TLS errors from this container, so newer entries there are not
checked.

## Short answer

1. **One new cell, from a known construction nobody had compared with the bipartite table:** the bipartite flag graph
   of PG(4,3) (Cames van Batenburg–Korsky's "bipartite compatibility graph" C(2,3), arXiv:2608.03965, Aug 2026) is
   **16-regular, bipartite, diameter 5, on 31,460 vertices**. The table's (16,5) value is 27,300 (+15.2 %). Checked
   all-pairs. It is not a Haar graph of any family build_haar2.py knows, so it is saved as an edge list (§1.1).
2. **The same idea gives a family for every building type,** with diameter equal to the Coxeter number. With a balanced
   diagram it is regular and tends to the bipartite Moore bound: odd D (type A_2k), D ≡ 0 mod 4 (type C_2m; checked
   on C_4(2): 9-regular, diameter 8, 160,650 vertices), D = 6, 12, 30. Inside our table range only (16,5) beats the
   table. D ≡ 2 mod 4 with D ≥ 10 (except 30) has no balanced diagram (§1.2).
3. **Our record connection sets have no formula.** Across 131 Haar records the normal form of S (classes of
   s_i⁻¹s_j) is indistinguishable from random (χ² = 3.4 on 2 d.o.f.), apart from a mild avoidance of short cycles.
   The metacyclic records (45 solutions) show no formula for (m, k, r, S) either. What *is* regular is the size:
   the size law of SIZE_LAW.md, which holds to ±2 % per cell across unrelated groups (§3).
4. **The table itself has three exact regularities.** Its green D = 5 and D = 7 values are (2j+1)·|polygon|, which
   the polygon-cover theorem explains (proved, and true for any bipartite base of even diameter). Its green D = 8 values are
   5·⌊(q+5)/2⌋·|GH(q)| in five cells and 15·|GH(11)| in a sixth. Nobody has published that construction; it is the
   main open lead (§2.1).
5. **Two simple general bounds,** both proved and checked against every cell: covers with two extra steps
   (D = n+2, ten copies with two matchings) and the doubling n_b(Δ, D) ≥ 2·n(Δ−1, D−1) from the general table. Neither
   beats the table, except that the doubling of Mizuno's (12,4) graph (5,832 vertices, general table) would give
   (13,5) ≥ 11,664 > 11,480. We do not have that graph (§1.3, §1.4).

---

## 1. Proved (with a computer check)

### 1.1 (16,5) ≥ 31,460: the A_4 flag graph over GF(3)

*Construction* (Cames van Batenburg–Korsky, §3 of arXiv:2608.03965; also Isham–Lakhotia–Monroe–Petrini,
arXiv:2608.27253, Thm 6.11). V = GF(q)⁵. One side: flags (W₁ ⊂ W₃), the other: flags (W₂ ⊂ W₄) (W_i of dimension i).
Join (W₁,W₃) to (W₂,W₄) when W₁ ⊂ W₂ ⊂ W₃ ⊂ W₄. Each vertex has (q+1)² neighbours (two independent choices in a
2-dimensional quotient), the edges are the complete flags, so the order is 2·[5]_q!/(q+1)². Diameter 5: any two
complete flags come from two orderings of one basis, and odd–even transposition sort reaches one from the other in
5 alternating rounds (their Lemma 2.1).

| q | Δ | vertices | table | check |
|---|---|---|---|---|
| 2 | 9 | 2,170 | 2,496 (ours 2,662) | flags.py BFS + apsp.c all-pairs: diameter 5 |
| 3 | 16 | **31,460** | 27,300 | flags.py BFS + apsp.c all-pairs: diameter 5, 16-regular, bipartite |

Files: `flags.py` (builds the graph from the definition), `graphs/d16D5_n31460_flagsA4_q3.edges.gz` (edge list,
uncompressed sha256 18a9cc6e183b6e644352bd2a73b664f56fe65eebce3eb42f5f038df6d7015528), `runs/d16D5_n31460_check.txt`,
`runs/C2_2_check.txt`. apsp.c is the coordinator's checker (research/lifts/coordinator_check/apsp.c, no symmetry
assumed). Neither paper compares C(k,q) with the bipartite table. CvB–K use it for the edge version; Isham et al. take
polarity quotients. So the (16,5) entry is new as far as we can tell. Credit goes to CvB–K for the graph; our part is
noticing that it beats the table. The current wiki value for (16,5) is unverified (wiki unreachable).

### 1.2 Flag graphs of other buildings (a family for each Coxeter type)

Let a spherical building of rank r have its Coxeter diagram (a tree) split into the two colour classes I₁, I₂. Take
as vertices the partial flags of type I₁ and of type I₂, adjacent when together they form a chamber. A vertex of type
I₁ has ∏_{i∈I₂}(q_i+1) neighbours. **Diameter ≤ the Coxeter number h** (= h in every case computed).

*Proof of ≤ h.* An I₁-vertex x is a residue R_x of type I₂, an I₂-vertex a residue of type I₁, and x ~ y iff
R_x ∩ R_y ≠ ∅. That intersection is then one chamber, since I₁ ∩ I₂ = ∅. A path x = x₀, x₁, …, x_ℓ gives
chambers C_i = R_{x_{i−1}} ∩ R_{x_i}, and C_i, C_{i+1} lie in a common residue of type I₁ or I₂ (alternately). So
d(x, y) ≤ ℓ iff the Weyl distance w = δ(C, C') of some C ∈ R_x, C' ∈ R_y is a product of ℓ − 1 alternating
elements of W_{I₁}, W_{I₂}. Since δ(R_x, R_y) is a double coset W_{I₂} w W_J, this says w is a product of ℓ + 1
alternating blocks. For a bipartite Coxeter element (c₁ = product of the I₁ reflections, c₂ likewise), both
c₁c₂c₁… and c₂c₁c₂… with h factors are reduced words for w₀ (Bourbaki, Lie Groups Ch. V §6 Ex. 2). Every w ≤ w₀ is
a subword of a reduced word for w₀ (subword property of Bruhat order), hence a product of h alternating blocks
starting with whichever class is needed. So d(x, y) ≤ h. ∎ With equal parameters and
|I₁| = |I₂| = r/2 the graph is (q+1)^{r/2}-regular of order 2·∏[d_i]_q/(q+1)^{r/2}, and the ratio to the bipartite
Moore bound tends to 1 as q → ∞.

Balanced diagrams: A_{2k} (h = 2k+1), B_{2m}/C_{2m} (h = 4m), G₂ (6), F₄ and E₆ (12), E₈ (30). So the bipartite
problem is asymptotically solved (lim n_b/Moore = 1 along prime powers) for every odd D and every D ≡ 0 mod 4, and for
D = 6, 12, 30. D ≡ 2 mod 4 with D ≥ 10, except 30, is not reached this way (A_{2k−1}, B_{odd}, D_n, E₇ are unbalanced,
and the unbalanced versions lose a power of q). I have not checked whether this bipartite statement is in the
literature.

Status: CvB–K prove the type-A case directly (odd–even sorting). The argument above uses only standard building
facts, but nobody else has read it. I checked it by computer on seven cases.
`bflags.py` → `runs/bflags_coxeter_check.txt` covers A₂–A₅ and C₂–C₄ over GF(2), balanced and unbalanced, and gives
eccentricity h from both sides every time: A₃ (degrees 3, 9) 4, A₅ (9, 27) 6, C₃ (3, 9) 6. `cflags.py` builds the
flag graph of W(7,2) (C₄, q = 2) separately. It is 9-regular with 160,650 vertices and has diameter exactly 8
(apsp all-pairs, `runs/C4_2_check.txt`). Orders for all types and q: `buildings.py` → `buildings_out.txt`. In the
table range (Δ ≤ 16, D ≤ 10) only A₄(3) beats the table. C₄(2) gives 160,650 at (9,8) (table 449,480) and C₄(3)
gives 23,878,400 at (16,8) (table 36,201,060).

Two ways to grow C(2,q) that fail:
- **Lifts.** Some same-side pairs at distance 4 in C(2,q) are joined by exactly one walk of length ≤ 4
  (`walkcount.c` → `runs/walkcount_C2q.txt`: minimum 1 for q = 2 and q = 3). So every voltage lift by a group ≠ 1 has diameter ≥ 6. Proof: the
  copies of such a target other than the one the unique walk reaches are at distance ≥ 6.
- **Affine versions.** Removing a hyperplane and/or a point from A₄(3) (12-regular, 18,720 vertices) raises the
  diameter to 8 (`flags_affine.py`, `runs/flags_affine_Hp_q3_check.txt`).

### 1.3 Polygon covers (any even-diameter base) and their saturation

*Statement.* Let B be a bipartite graph of even diameter n with equal colour classes, and σ₁…σ_j perfect matchings
between the classes. Lift B + matchings by Z_M with voltage 0 on B and t_i on σ_i.
- (n+1) If M = 2j+1 and T = {1..j}, the lift has diameter ≤ n+1 for any matchings. This is the proof in
  research/lifts LITERATURE.md §5, which only uses "same-colour distance ≤ n, opposite-colour distance ≤ n−1", true
  in every bipartite graph of even diameter n.
- (n+2) If {0} ∪ ±T ∪ (T−T) ∪ (T+T) = Z_M, the lift has diameter ≤ n+2 for any matchings. Two hops cost 2 steps
  and leave a geodesic of length ≤ n. For j = 2 the largest M is **10** (T = {1,4}).

Check: `pcover.c` with 0 annealing steps (random matchings) gives cost 0 for W(3), W(4) at D = 6 and for GH(2) at D = 8
with Z₁₀, T = {1,4}, three seeds each. A scan of all T ⊂ Z_M for M = 10…13 finds only T = {1,4} and {2,3} at M = 10
(`runs/zero_voltage_n2_gq3.txt`).

*What it explains.* Every green D = 5 and D = 7 table value is (2j+1)·|GQ(q)| or (2j+1)·|GH(q)| with Δ = q+1+j
(`table_factor.py` → `table_factor_out.txt`; (16,5) = 27,300 is the exception). Our own D = 4 and D = 6 graphs
(Theorems A, C1, R) as bases do not beat any D = 5 or D = 7 cell: the multiplier 2j+1 per j extra degrees is too
small to make up for the smaller base. The n+2 version gives 10·|GH(q)| at D = 8 against the table's 30–45·|GH(q)|.

*More than 2j+1 copies at D = n+1 (negative so far).* A copy outside {0, ±T} can only be reached by two-hop routes,
and each covers at most 1 + 3q(q+1) points from a point source. With j = 2 and Z₇ (T = {1,3}) the counting allows
it for q ≤ 5 only (69/40, 111/85, 163/156 route slots per point class). Annealing the matchings on W(3) + 2 matchings
over Z₇ (`pcover.c`, 3 seeds × 4·10⁵ moves) stalls at 206–238 uncovered pairs (`runs/pc_gq3_M7_s*.log`). Not
pursued further.

### 1.4 The doubling bound n_b(Δ, D) ≥ 2·n(Δ−1, D−1)

B(H): two copies of V(H), x₀ ~ y₁ iff x = y or xy ∈ E(H). If H has degree Δ−1 and diameter D−1, then B(H) is
bipartite of degree Δ and diameter ≤ D (go along a shortest path, use the loop once to fix the parity). For a
Cayley graph H = Cay(G, T) this is the Haar graph H(G, T ∪ {e}). `double_bound.py` compares 2·n(Δ−1, D−1)
(Wikipedia's general table, raw wikitext saved in `data/`, "as of 14 October 2026") with the bipartite table and our
records in every cell (`double_bound_out.txt`). It beats both in exactly one cell: **(13,5), 2·5,832 = 11,664 >
11,480**, using the (12,4) graph credited to Mizuno 2026 on the wiki. Mizuno's arXiv paper 2606.15860 is about
(12,5) and (16,5), not (12,4), and I did not find the (12,4) graph, so this is not built. Elsewhere the ratio is
0.1–0.99 (it reaches 0.99 at D = 3).

## 2. Conjectured, with strong evidence

### 2.1 The green D = 8 table values are m(q)·|GH(q)|

`table_factor_out.txt`: (10,8) = 30·|GH(7)|, (11,8) = 30·|GH(8)|, (12,8) = 35·|GH(9)|, (14,8) = 40·|GH(11)|,
(16,8) = 45·|GH(13)|, all with Δ = q+3; (13,8) = 15·|GH(11)| with Δ = q+2; (15,8) repeats (14,8). The five Δ = q+3
values fit **m = 5·⌊(q+5)/2⌋** exactly. Two extra edges per vertex, and a factor 5 = 2j+1 as in the D = 7 cover.
The extra factor ⌊(q+5)/2⌋ grows with q, so the construction must use the polygon's own paths (non-zero voltages on
GH). The zero-voltage covers of §1.3 top out at 10 copies, so they cannot do it.

Random voltages cannot do it either. Take GH(7) + 2 matchings over Z_m (Δ = 10). Each base vertex has about 274 walks
of odd length ≤ 7 per base target, i.e. 274/m per target copy. With no symmetry all 39,216 base vertices are sources,
so the expected number of misses is ≈ 39,216 · 19,608 · m · e^{−274/m}. That is about 20 only at m ≈ 13 (the lifts
job's estimate of 12). Even with an automorphism group acting freely with a handful of orbits, the same count stops near
m ≈ 25. The table has m = 30, so the construction is genuinely structured. Its vertex count can be rewritten as
5·(#flags + 2·#elements of GH(q)) for odd q. A numerical hint: the factor m/5 is (q+1)/2 + 2 for odd q
and q/2 + 2 for q = 8, and those are |image of a quadratic map x ↦ x² + bx on GF(q)| + 2 (squares for odd q,
trace-0 elements for even q). That suggests copies indexed by the values of a quadratic form plus two extra
classes, rather than a group of order m. The one Δ = q+2 value, 15 = 3·5 at q = 11, does not fit the same rule;
5 = (q−1)/2 there. A structured construction, if found, is the
natural route to the cells (10,8), (12,8), (14,8), (16,8), which random-like Haar search cannot reach (SIZE_LAW §3.3,
STRUCTURE.md §6). Not found in this session. Web searches for the source (Delorme–Gómez–Quisquater, the numbers
themselves) found nothing.

### 2.2 The size law is a property of (Δ, D), not of the group

Best record per cell (`tabulate.py` → `records.json`, `tabulate_out.txt`): N/(Δ−1)^{D−2} = 0.98–1.20 at D = 8, 0.80–0.97
at D = 9, 0.67–0.80 at D = 10. In each D it rises slowly with Δ, as SIZE_LAW.md's C_D = Δg/ln(N/μ*) predicts.
Across groups it barely moves. At (5,10), fourteen different metacyclic groups (and SL(2,13) × Z21) solved within
N = 45,864–47,736, a spread of 4 %. At (5,9) eight groups lie within 3 %, at (4,10) three within 4 %
(`meta_table_out.txt`). Ours/table: 1.03–1.28 at D = 8, 1.08–1.25 at D = 9, 1.08–1.20 at D = 10.

### 2.3 Where we stand against the Moore bound

`cells.py` → `cells_out.txt` gives best known / bipartite Moore bound for every cell (* = ours). Within each column the
ratio falls slowly with Δ. Our weakest cells relative to Moore are the ones held by structured families we cannot
search: D = 5 with Δ = 10–15 (0.24–0.27, polygon covers), D = 7 with Δ = 7 and 9–16 (0.15–0.21, hexagon covers) and
D = 8 with Δ = 10, 12, 14, 16 (0.10–0.11, the unexplained GH family). The new (16,5) entry is 0.29.

## 3. Weak patterns

- **S in the Haar records is random-like** (`stats_S.py` → `stats_S_out.txt`; 96 records over SL/PSL(2,q), q odd,
  4,178 quotients s_i⁻¹s_j). Split/elliptic/parabolic counts 2050/1998/130 against 2011/2017/149 expected for uniform
  elements, χ² = 3.37 (5 % critical value 5.99). Quotients of full order ≤ 6 (each gives a cycle of length ≤ 12
  through every vertex): 41 observed against 56.4 expected (about 2σ low). The annealing mildly avoids short cycles.
  Girths: 8 or 10 in almost all records, 6 in the f = 3 orbit records (commuting torus letters, as STRUCTURE.md §8 says).
- **n is not tied to q.** The pairs (q, n) in the records (`tabulate_out.txt`) follow only from hitting a target
  order N ≈ |Q|·n. The orbit records have every prime of n ≡ 1 mod 3, by design (STRUCTURE.md §2). No n | q ± 1 pattern.
- **Metacyclic records** (`meta_table.py` → `meta_table_out.txt`, 45 solutions, D = 5–10): 39/45 have a faithful
  action (ord_m r = k), 11/45 have m prime, and m is otherwise any composite. The abelianisation is small (|G^ab| is
  0.03–1.7 % of N for D ≥ 8). The j-parts of S follow no pattern. No formula for (m, k, r, S).

## 4. Dead ends (tested and dropped)

| idea | test | result |
|---|---|---|
| a formula for S across q in the Haar records | normal forms, class statistics (§3) | random-like; nothing to extrapolate |
| more than 2j+1 copies at D = n+1 with zero polygon voltages | counting + annealing, W(3) + 2 matchings, Z₇ | stalls at 206–238 uncovered pairs |
| affine/bi-affine A₄(3) flag graphs (12-regular, 18,720 vertices) | flags_affine.py + apsp | diameter 8, not 5 |
| C₄ flag graphs at (9,8), (16,8) | buildings.py, cflags.py | 160,650 < 449,480; 23.9 M < 36.2 M |
| covers of our D = 4 / D = 6 records to D = 5 / D = 7 | §1.3 arithmetic | below the table in every cell |
| edge-transitive coset graphs Cos(G; ⟨a⟩, ⟨b⟩), a, b of order Δ (Conder's (3,7) graph has this form) | coset.py on PSL(2,7), (2,11), (2,13) with Δ = 3 (all pairs) and PSL(2,17) with Δ = 4 (200 pairs) → `runs/coset_cubic.txt` | at most 112 vertices at D = 7, 440 at D = 10, 1,224 at (4,8) (table 2,184). The vertex stabiliser ⟨a⟩ clumps misses by Δ, but its fixed points (≈ 4|T|/Δ in PSL(2,q)) are missed with probability e^(−λ/Δ). It is the one-orbit case of STRUCTURE.md §2.5 |
| voltage lifts of C(2,q) to keep D = 5 with more vertices | walkcount.c | impossible: unique walks (§1.2) |
| delete vertices/edges of C(2,3) to get Δ = 15 (31,460 vertices vs 20,497 needed) | walkhist.py → `runs/walkhist_C23.txt` | 11,664 of the 15,525 same-side targets at distance 4 have exactly one walk of length ≤ 4, so almost any deletion breaks diameter 5 |

## Scripts and outputs (this folder)

| script | output | what |
|---|---|---|
| recs.py | – | parser for research/frontier/sols (haar_gen3 format), group arithmetic |
| tabulate.py | tabulate_out.txt, records.json | one row per record, normal forms, girth, ball growth |
| stats_S.py | stats_S_out.txt | class statistics of S against random |
| meta_table.py | meta_table_out.txt | metacyclic records (meta_sols/ copies the lifts-branch solutions) |
| table_factor.py | table_factor_out.txt | factorisation of the table against polygon sizes |
| general_table.py, double_bound.py | double_bound_out.txt | B(H) doubling against the general table |
| polygons.py, pcover.c | bases/, runs/pc_*, runs/zero_voltage_n2_gq3.txt | polygon covers |
| flags.py, flags_affine.py, cflags.py, bflags.py, buildings.py, walkcount.c | graphs/, runs/*check*, buildings_out.txt | building flag graphs |
| coset.py | runs/coset_cubic.txt | coset graphs with cyclic stabilisers |
| cells.py, walkhist.py | cells_out.txt, runs/walkhist_C23.txt | per-cell Moore ratios; walk multiplicities in C(2,3) |
