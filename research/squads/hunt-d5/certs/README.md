# hunt-d5 exact searches (certificates)

All searches use `tools/haar5` (Haar graph H(G,S), |S| = Δ, diameter ≤ 5 iff (S⁻¹S)² = G = (SS⁻¹)²) on GAP SmallGroups
tables (`tools/gapgroup.py`, identity = index 0). A set is first tested against up to 256 learned "probe" elements
(cheap single-element membership tests); any set with cost 0 covers every probe, so it is never skipped: the searches
are exact for the question "is there a cost-0 S?". The printed `min` is the minimum over the sets that passed the
probes (an upper bound on the true minimum), not the exact minimum.

| file | question | sets | answer |
|---|---|---|---|
| d5_haar_orders_193_203.log, d5_haar_orders_204_215.log | (5,5): S ∋ e, all 4-subsets, every group of order 193–215 (179 groups, `haar5 exhp`) | 5.5–8.7·10⁷ per group | no Haar graph of diameter ≤ 5 |
| d5_haar_order_176_positive_control.log | the same search on order 176 | | finds SmallGroup(176,15) (our 352-vertex graph): the search works |
| d6_haar_355_1_C71xC5.log | (6,5): S ⊇ {e, r}, r one representative per Aut(G)-orbit (5 orbits), all 4-subsets (`haar5 complete`) | 5 × 6.4·10⁸ | none: C71 ⋊ C5 has no (6,5) Haar graph |
| d6_haar_351_12_F27xC13.log | the same for SmallGroup(351,12) = F₂₇ ⋊ C13 (5 orbits) | 5 × 6.0·10⁸ | none |
| d6_haar_357_1.log | the same for SmallGroup(357,1) = C17 × (C7 ⋊ C3) (7 orbits) | 7 × 6.5·10⁸ | none |
| d6_haar_360_51_C3xSL25.log, d6_haar_351_5.log | (6,5) SmallGroup(360,51) = C3 × SL(2,5) and SmallGroup(351,5): rank-0 pass (`haar5 complete` with core {e, r₀}, r₀ in the largest orbit) plus `haar5 cert … 1` (ranks ≥ 1, see below); orbit files orbits_*.txt | 6.7·10⁸ + 6.7·10⁷ and 6.1·10⁸ + 1.4·10⁷ | none |
| d6_haar_351_1.log … d6_haar_351_14.log (with d6_haar_351_5.log, d6_haar_351_12_F27xC13.log above) | (6,5) **all 14 groups of order 351** (C13 ⋊ C27, C351, C9 × (C13 ⋊ C3), three C13 ⋊ (C9 ⋊ C3), C3 × (C13 ⋊ C9), C13 ⋊ ((C3 × C3) ⋊ C3), C117 × C3, C13 × ((C3 × C3) ⋊ C3), C13 × (C9 ⋊ C3), (C3)³ ⋊ C13, C3 × C3 × (C13 ⋊ C3), C39 × C3 × C3): `haar5 cert` from rank 0 (`tools/cert_queue.sh`) | 6.1–6.2·10⁸ each | **none: no (6,5) Haar graph on 702 vertices** |
| d6_haar_360_136.log, d6_haar_360_88.log | (6,5) SmallGroup(360,136) and (360,88), both of shape (C3 × C3) ⋊ (C5 ⋊ Q8) with |G/G'| = 4 (farms: cost 4 in 31 of 31 seeds, and cost 6): `haar5 cert` from rank 0 | 7.2·10⁸ each | none |
| d6_haar_343_4.log | (6,5) SmallGroup(343,4) | 6.1·10⁸ | none |
| d7_haar_610_2_coset_patterns.log (patterns: d7_patterns_610_2.txt) | (7,5) SmallGroup(610,2) = C2 × (C61 ⋊ C5) = `meta 61 10 9 1`: every coset pattern (599 classes), normalized S inside each (`haar5 prod`, see below) | 7.6·10⁹ | **none: no (7,5) Haar graph on this group** |
| d7_haar_615_1_coset_patterns.log (patterns: d7_patterns_615_1.txt) | (7,5) SmallGroup(615,1) = C3 × (C41 ⋊ C5) = `meta 41 15 10 1` (cost 2 five times in about 1,000 farm seeds): every coset pattern (3,935 classes) | 1.3·10¹⁰ | **none** |
| d7_haar_618_2_coset_patterns.log (patterns: d7_patterns_618_2.txt) | (7,5) SmallGroup(618,2) = C2 × (C103 ⋊ C3) = `meta 103 6 56 1` (cost 4 in 7 of 100 farm seeds): every coset pattern (75 classes) | 5.0·10⁹ | none |
| prod_completeness_checks.log | end-to-end check of the coset-pattern search on six small groups at Δ = 5 (`tools/jcheck.py`: cyclic quotient, a kernel in the action, Z_n factors, groups with and without solutions): brute force (`haar5 exhp`) and `haar5 prod` give the same set of pattern classes containing a cost-0 set | up to 7.4·10⁵ solutions | MATCH in all six |
| d7_prod_positive_control_506.log | the same method on `meta 23 11 2` × Z2 (order 506) in the pattern of a known solution | 2.7·10⁵ | finds 2 solutions, one of them the known one (scaled by u = 11) |
| d7_haar_615_1_orbit_spaces.log | (7,5) SmallGroup(615,1): every S that is a union of e, fixed points and orbits of an automorphism of order 2–5 (`haar5 exho`) | | minimum ≥ 12 in every space |
| d7_haar_615_1_3swap_of_cost{4,2}_set.log | (7,5) SmallGroup(615,1): all sets within 3 swaps of the cost-4 set S = 0 206 135 160 343 459 282 and of the cost-2 set S = 0 206 135 343 507 543 593 (`tools/nbhd.py … 3`) | 20 × 3.8·10⁷ each | found the cost-2 set; nothing of cost 0 |

Reduction used for the (6,5) certificates: H(G,S) ≅ H(G, S s⁻¹) ≅ H(G, φ(S)) for s ∈ S, φ ∈ Aut(G). Given any S, translate
so that e ∈ S, pick another element t ∈ S and apply φ with φ(t) = the chosen representative of t's Aut(G)-orbit. So if
some S works, one containing {e, r} works for some representative r. Orbit representatives: `gapgroup.py orbits N I`.
Card a2 of round 3 ran the (5,5) search for orders 217–223 (r3/a2/results.txt): none.

`haar5 cert` (added later in the session) sharpens the reduction: right quotients s_j s_i⁻¹ are invariant under right
translation and are permuted by Aut(G). Rank the Aut-orbits on G \ {e}, largest first. A cost-0 S can be translated and
moved by an automorphism so that it contains e and the representative r_k of the lowest-ranked orbit k among its right
quotients, with every right quotient of rank ≥ k. So for each k only sets {e, r_k, …} with all pairwise right quotients
of rank ≥ k are enumerated; later ranks are tiny, and the total is about one rank-0 pass. Positive control: on
SmallGroup(176,15) it lists 640 normalized solutions (apsp VALID on one, 352 vertices).

Coset-pattern search (`tools/jpatterns.py`, `tools/jexact.py`, `haar5 prod`), for G = (Z_p ⋊_r Z_k) × Z_n with G' = Z_p:
the cosets of G' met by S form a multiset J in G/G' = Z_k × Z_n. Translating S so that e ∈ S puts (0,0) in J; all
translates of J that keep a point at (0,0), and −J (S → S⁻¹ swaps the sides), give the same graphs, so one J per class is
searched. Inside a class: conjugation by (b,0,0) adds (r^j − 1)b to the a-part of an element of coset (j,z), so the first
element with r^j ≠ 1 can be taken to be (0, j, z); then the automorphisms (a,j,z) ↦ (ua, j, z), u ∈ Z_p^*, fix e and that
element and scale a second element to a ∈ {0, 1}; all other elements range over their cosets. Every S is equivalent to
one of these products, so `haar5 prod` over all classes is exact for cost 0. Classes are searched in order of
mu_J = Σ_t p·exp(−W_t/p) (W_t = words of length ≤ 4 landing in coset t), the expected cost of a random S with that pattern.
