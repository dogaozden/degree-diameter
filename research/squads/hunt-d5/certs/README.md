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
| d7_haar_615_1_orbit_spaces.log | (7,5) SmallGroup(615,1): every S that is a union of e, fixed points and orbits of an automorphism of order 2–5 (`haar5 exho`) | | minimum ≥ 12 in every space |
| d7_haar_615_1_3swap_of_cost{4,2}_set.log | (7,5) SmallGroup(615,1): all sets within 3 swaps of the cost-4 set S = 0 206 135 160 343 459 282 and of the cost-2 set S = 0 206 135 343 507 543 593 (`tools/nbhd.py … 3`) | 20 × 3.8·10⁷ each | found the cost-2 set; nothing of cost 0 |

Reduction used for the (6,5) certificates: H(G,S) ≅ H(G, S s⁻¹) ≅ H(G, φ(S)) for s ∈ S, φ ∈ Aut(G). Given any S, translate
so that e ∈ S, pick another element t ∈ S and apply φ with φ(t) = the chosen representative of t's Aut(G)-orbit. So if
some S works, one containing {e, r} works for some representative r. Orbit representatives: `gapgroup.py orbits N I`.
Card a2 of round 3 ran the (5,5) search for orders 217–223 (r3/a2/results.txt): none.
