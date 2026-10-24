# Voltage lifts: results (voltage-lifts job, 2026-10-23)

## Summary

- **Five cells taken from the table.** Every graph was checked four ways: lift.c's BFS; an independent Python
  rebuild; all-pairs BFS with no symmetry assumed; and, for Haar graphs, the repo's build_haar2.py. Details in §2.0.

  | cell | table (holder) | ours | construction |
  |---|---|---|---|
  | (3,8) | 256 (Delorme–Gómez–Quisquater) | **288** | lift of a 2+2 cubic base over Z3² ⋊ Z8 (not a Haar graph) |
  | (5,8) | 9,234 (Loz) | **9,316** | Haar graph of Z137 ⋊₁₆ Z34 |
  | (4,10) | 11,748 (Loz) | **11,988** | Haar graph of Z333 ⋊₈₃ Z18 |
  | (5,9) | 27,936 (Loz) | **28,842** | Haar graph of Z437 ⋊₂₆ Z33 |
  | (5,10) | 90,068 (Loz) | **95,472** | Haar graph of Z1989 ⋊₄₆₁ Z24 |

  The Haar values may still rise; the last sweeps were still finding solutions.
- **Exact rebuilds of table records**, proved isomorphic with BLISS:
  - (7,3) 80, from the only published voltage assignment;
  - (3,7) 168, Conder's graph, as a 2+2-base lift;
  - (4,7) 840, the Bond–Delorme graph, which turns out to be Haar(A5 × Z7).
  - Also (10,5) 4000 and (7,7) 23436 by an explicit polygon-cover construction that reproduces every green D = 5 and
    D = 7 value of that form.
- **Negative results with reasons:**
  - (3,7) and (4,7) above the table;
  - the polygon-cover family (saturated at 2j+1 copies);
  - the green D = 8 cells (about 2.5× beyond random lifts);
  - a girth obstruction (proved) that rules out lifts of GH/GQ incidence graphs below D = g − 1;
  - (3,10), with two cost-2 near misses closed by exhaustive search;
  - (6,5), floor at cost 4.

All runs were made in this cloud session (4 cores, 15 GB), each with a time limit. Table values are from
research/frontier/TABLE.md, which agrees with the CombinatoricsWiki (LITERATURE.md §1). "Moore" is the bipartite
Moore bound.

## 1. Validation: table records rebuilt exactly

Every graph below passes three checks:
- `lift check`: lift.c's own BFS;
- `verify_lift.py`: an independent rebuild of the group and the lift, an automorphism check, and BFS;
- `apsp`: all-pairs BFS on the edge list, with no symmetry assumed.

Where the record's adjacency list is published, `compare_iso.py` also tests isomorphism with igraph's BLISS. Outputs
are in `verify/`.

| cell | table | our lift | how it was obtained | isomorphic to the published graph? |
|---|---|---|---|---|
| (7,3) | 80 (optimal) | dipole, 7 edges, Z5 ⋊₂ Z8 | the **published** voltages (Feria-Purón–Miller–Pineda-Villavicencio 2013, p. 389), inverted for our convention | **yes**, to Hafner's `7.3` (\|Aut\| = 7680) |
| (3,7) | 168 | 2+2 cubic base (biadjacency ((2,1),(1,2))), (Z7 ⋊₂ Z3) × Z2 | found by lift.c in 113 evaluations | **yes**, to Conder's `mdec3.7` (\|Aut\| = 504) |
| (4,7) | 840 | Haar graph (dipole, 4 edges) of PSL(2,5) × Z7 = A5 × Z7 | Aut of Hafner's `4.7` (Bond–Delorme) has a colour-preserving regular subgroup A5 × Z7 (centre Z7, derived subgroup A5); lift.c then re-finds the graph in < 1 s | **yes**, three independent seeds (\|Aut\| = 2520) |
| (10,5) | 4000 | W(7) incidence + 2 random perfect matchings, Z5; voltages 0 on W(7), t on matching t | the (2j+1)-fold polygon cover (LITERATURE.md §5) | the original (Delorme–Gómez–Quisquater) is unpublished; same order and degree, diameter 5 |
| (7,7) | 23436 | H(5) incidence + 1 random perfect matching, Z3 | same construction | same order and degree, diameter 7 |

Solution files: `sols/rebuild_*.txt`.

**Two findings from the rebuilds.**
- The (4,7) record is a Haar graph of a non-metabelian group, A5 × Z7. The repo's Haar searches at (4,7) used only
  metacyclic groups (research/frontier/wave4), and so did the Loz-type searches (LITERATURE.md §3). That points at
  non-metabelian groups for the other small cells; see §2.
- All green D = 5 and D = 7 values that fit the formula come from one trivial construction (polygon + j arbitrary
  matchings, Z_{2j+1}). The proof is in LITERATURE.md §5.

## 2. Attack on the missing cells

### 2.0 New records so far

| cell | table (holder) | ours | construction | file |
|---|---|---|---|---|
| (3,8) | 256 (Delorme–Gómez–Quisquater) | **288** (+12.5 %) | 2+2 cubic base (biadjacency ((2,1),(1,2))) over Z3² ⋊_M Z8, M = [[0,2],[1,0]] | `sols/c1r_d3D8_n288_b2_3_0_aff302108_s1.txt` |
| (5,8) | 9,234 (Loz) | **9,316** (+0.9 %) | Haar graph of Z137 ⋊₁₆ Z34 (metacyclic) | `sols/d5D8_n9316_haar_meta137_34_16.txt` |
| (4,10) | 11,748 (Loz) | **11,988** (+2.0 %) | Haar graph of Z333 ⋊₈₃ Z18 (metacyclic) | `sols/d4D10_n11988_haar_meta333_18_83.txt`. Also 11,772 (Z218 ⋊₃ Z27) |
| (5,10) | 90,068 (Loz) | **95,472** (+6.0 %) | Haar graph of Z1989 ⋊₄₆₁ Z24 (metacyclic) | `sols/d5D10_n95472_haar_meta1989_24_461.txt`. Also 93,738, 93,704, 93,444, 93,310, 93,240, 93,196, 93,166, 93,120, 93,000, 92,492, 92,318, 91,938, 91,812, 91,756 and 91,728 (SL(2,13) × Z21) |
| (5,9) | 27,936 (Loz) | **28,842** (+3.2 %) | Haar graph of Z437 ⋊₂₆ Z33 (metacyclic) | `sols/d5D9_n28842_haar_meta437_33_26.txt`. Also 28,560, 28,444, 28,418, 28,094, 27,972 and 27,948 |

All checks pass: lift check, verify_lift.py, and apsp all-pairs, which assumes no symmetry. The Haar graphs also pass
the repo's build_haar2.py:
- (5,10) 95,472: sha256 67342fdc…;
- (5,10) 93,738: sha256 82b66432…;
- (5,10) 93,444: sha256 d3c643b9…;
- (5,10) 93,000: sha256 eca54823…;
- (5,10) 92,492: sha256 6be113dc…;
- (5,10) 92,318: sha256 0aedd296…;
- (5,10) 91,938: sha256 73dc7fc3…;
- (5,10) 91,812: sha256 90994a5f…;
- (5,10) 91,756: sha256 a28102a9…;
- (5,10) 91,728: sha256 32998e69…;
- (5,8) 9,316: sha256 dabe25b3…. A networkx all-pairs diameter is also in
  `verify/d5D8_n9316_haar_meta137_34_16.networkx.txt`;
- (4,10) 11,988: sha256 8528201d…. A networkx all-pairs diameter is also in
  `verify/d4D10_n11988_haar_meta333_18_83.networkx.txt`;
- (4,10) 11,772: sha256 4665f9f1…, with networkx in `verify/d4D10_n11772_haar_meta218_27_3.networkx.txt`;
- (5,9) 28,842: sha256 aab0d5cb…;
- (5,9) 28,560: sha256 5b6247d3…;
- (5,9) 28,444: sha256 766dfcd6…;
- (5,9) 28,418: sha256 918ae59c…;
- (5,9) 28,094: sha256 d0a736d4…;
- (5,9) 27,972: sha256 01da8334….

Outputs are in `verify/`.

**(5,9).**
- Connection set of the 28,842 graph in Z437 ⋊₂₆ Z33, elements (a, j): (0,0), (405,18), (222,4), (372,17), (102,5).
- Found by haar_cell.py: haar_gen3 annealing on the RANDSAMPLE-screened metacyclic candidates. The first sweep's six orders took 24 s, 5 s, 303 s, 10 s, 206 s and 328 s. N = 14,280 was the top of its window.
- A second sweep (12,813 screened candidates, N = 14,210–14,700) solved N = 14,421 in 70 s. Above it, N = 14,531,
  14,607 and 14,634 stalled at cost 2–4.
- N = 14,133 (Z673 ⋊ Z21) stalled at cost 2 on two seeds.
- The cell was "marginal" (−1.7 %) in the size law and had never been run. Loz's 27,936 is itself a metabelian Haar
  graph search result (LITERATURE.md §3), so this is a modest gain from a stronger search, not a new structure.

**(3,8) = 288.** Voltages (aff "x,y,j"; base edges 0–2 ×2, 0–3, 1–2, 1–3 ×2):

| edge | 0–2 | 0–2 | 0–3 | 1–2 | 1–3 | 1–3 |
|---|---|---|---|---|---|---|
| voltage | 0,0,0 | 2,0,3 | 0,0,0 | 0,0,0 | 1,1,3 | 1,1,2 |

- 3-regular, bipartite, diameter 8, girth 12. Edge-list sha256 9dbc8e8f….
- \|Aut\| = 144, with 2 vertex orbits of 72 white + 72 black vertices each, so some automorphisms swap the colours.
  The colour-preserving automorphisms are exactly the 72 translations of the voltage group, with 4 orbits.
- So the graph is **not** a Haar graph: an exhaustive Haar search over Z3² ⋊ Z16, the group with Aut's element-order
  profile, finds no diameter-8 graph (best cost 6). A 2+2 base is genuinely needed.
- The group Z3² ⋊ Z8 is metabelian but not metacyclic. It came from the `aff` family added this session.
- It was found in 41 evaluations.
- Two later pushes (orders 290–348, with every rich group including the composite-modulus and 3-dimensional affine
  families) found nothing above 288. The best was cost 10 at n = 320.

**(5,10) = 95,472, with fourteen smaller orders found on the way.**
- 95,472 is a Haar graph of Z1989 ⋊₄₆₁ Z24. Connection set (a, j): (0,0), (826,18), (423,7), (1635,11), (993,10).
  - It came from the sweep N = 47,501–48,500 (36,804 screened candidates).
  - Seven candidates of order 47,509–47,736 had stalled at cost 1, including the same group Z1989 ⋊ Z24 with the
    action r = 383. The action r = 461 then solved.
- 93,738 is a Haar graph of Z919 ⋊₈ Z51. Connection set (a, j): (0,0), (66,6), (262,32), (432,27), (410,7).
  - It came from the re-screened sweep (27,309 candidates, N = 46,723–47,500), on its second attempt at this order.
    In the third sweep the same order had stalled at cost 1.
  - Above it, N = 46,956 stalled at cost 1 on two seeds.

- 93,444 is a Haar graph of Z1797 ⋊₂₁₂ Z26. Connection set (a, j): (0,0), (864,15), (1592,17), (395,21), (1058,12).
- It came from the third sweep (35,386 screened candidates, N = 46,501–47,500).
- In that sweep, N = 46,580 and N = 46,869 stalled at cost 1. Re-screened sweeps (N = 46,723–47,500 and
  47,501–48,500) are running.
- 93,000 is a Haar graph of Z775 ⋊₁₃₃ Z60. Connection set (a, j): (0,0), (227,14), (27,1), (508,42), (310,38).
  It solved after 168 s, at the top order of the second sweep's window (N = 46,500).
- 92,318 is a Haar graph of Z1489 ⋊₆₁ Z31. Connection set (a, j): (0,0), (909,30), (656,18), (378,4), (1082,9).
  It was found by the second sweep (18,989 screened candidates, N = 45,970–46,500) after 82 s of annealing.
- 91,938 is a Haar graph of Z1393 ⋊₁₈ Z33. Connection set (a, j): (0,0), (629,6), (1362,20), (900,23), (1300,8).
  Found after 24 s of annealing.
- 91,812 is a Haar graph of Z1093 ⋊₂₀₈ Z42, found by the same sweep after 113 s of annealing.
- 91,756 is a Haar graph of Z3277 ⋊₁₂₉ Z14. Connection set (a, j): (0,0), (1169,3), (2805,11), (952,5), (1779,4).
  It was found by haar_cell.py: 7,704 screened candidates of order 45,865–46,100, then 46 s of annealing.
- 91,728 was the first find, a Haar graph of SL(2,13) × Z21. Connection set (matrix | z):
  - [[1,0],[0,1]] | 0
  - [[3,8],[0,9]] | 16
  - [[2,7],[7,12]] | 7
  - [[1,10],[10,10]] | 2
  - [[8,3],[9,10]] | 5
  It was found by haar_gen3 in 9 s (2·10⁵ evaluations), after RANDSAMPLE screening put SL(2,13) × Z21 first
  (random-set minimum cost 13). μ at this order is 22.5.
- The size law predicted the cell as "marginal" (+0.7 %) but nobody had run it.

**(5,8) = 9,316.**
- Haar graph of Z137 ⋊₁₆ Z34. Connection set (a, j): (0,0), (47,2), (45,9), (5,31), (115,1).
- Found by haar_cell.py after 171 s (N = 4,618–4,760 window). The size law had called this cell "can't" (−6.6 %).
  The lift sweeps over orders 9236–9500 had found nothing.

**(4,10) = 11,988.**
- Haar graph of Z333 ⋊₈₃ Z18. Connection set (a, j): (0,0), (192,11), (31,13), (130,12).
- Found by haar_cell.py: 3,873 screened candidates, N = 5,875–6,050.
  - 11,772 (Z218 ⋊₃ Z27; (0,0), (187,2), (27,24), (139,23)) came first, in 2 s.
  - N = 5,887 and 5,964 stalled at cost 4.
  - At N = 5,994 the action r = 86 stalled at cost 1, while r = 83 solved.

### 2.1 Earlier record: (3,8) = 258, a Z43-lift of K3,3

`sols/c1r_d3D8_n258_b3_3_2_cyc43_s1.txt`: a **Z43-lift of K3,3**. Gauge-fixed voltages:

| base edge | 0–3 | 0–4 | 0–5 | 1–3 | 1–4 | 1–5 | 2–3 | 2–4 | 2–5 |
|---|---|---|---|---|---|---|---|---|---|
| voltage in Z43 | 0 | 0 | 0 | 0 | 7 | 26 | 0 | 1 | 16 |

- 258 vertices, 3-regular, bipartite, diameter 8, girth 12.
- \|Aut\| = 129 (= 3·43), with 4 vertex orbits.
- Verification (`verify/c1r_d3D8_n258_b3_3_2_cyc43_s1.txt`):
  - `lift check` VALID;
  - `verify_lift.py --full`: independent rebuild, right translations are automorphisms, networkx all-pairs diameter
    8, VALID;
  - `apsp`: all-pairs diameter 8.
- Edge-list sha256: 7dd94ad7fe2b999a87a23979badb0a5eab5f4df1daa2abb54bc740a99eb90f77.
- The table value 256 is Delorme–Gómez–Quisquater's (green). The Moore bound is 510.
- **Exhaustive limit for this family:** among all Z_N-lifts of K3,3 (N⁴ gauge-fixed assignments each),
  - N = 43 has diameter-8 solutions;
  - N = 44, 45, 46, 47, 48 have none (best costs 10, 16, 22, 26, 28).
  - The other bases and groups for orders 260–300 are in §2.2.

### 2.2 Every cell of the task: status

Ordering. The user asked to start where the table is furthest below the Moore bound and the record is oldest. That
points at the green D = 8 cells with Δ ≥ 10 (2n/Moore ≈ 0.10; Delorme–Gómez–Quisquater, unpublished). For them, and
for the other green large-Δ cells, the analysis and small-scale tests of §3 come first. They show that random-voltage
lifts cannot reach these values, and searching them at N ~ 10^5–10^7 would only confirm it. The compute therefore
went to the small cells, ranked by μ = N e^(−W/N) at the table order (SIZE_LAW.md §8): (3,8) 18, (5,10) 19, (5,9) 29,
(3,10) 31, (3,9) 34, (6,5) 35, (4,10) 39, (5,8) 41, (5,7) 47, (4,9) 47, (4,8) 54.

| cell | table (holder) | Moore | best found here | status |
|---|---|---|---|---|
| (6,5) | 684 (Loz) | 1,562 | – | negative so far. Rich and wide lift sweeps over orders 686–720: best cost 4 at 702 (Haar of GF(27) ⋊ Z13 = Z3³ ⋊ Z13, the `aff3` family); 7 further 300 s runs on that group all stop at cost 4 |
| (10..15,5) | 4000, 5850, 8200, 11480, 14760, 20496 (DGQ) | | rebuilt 4000 = (2j+1)·GQ | §3.2: the polygon family stops at 2j+1 copies; Haar can't (SIZE_LAW §3.3, −10 % to −29 %) |
| (16,5) | 27300 (DGQ) | 108,482 | – | not of the polygon form; not run |
| (3,7) | 168 (Conder et al.) | 254 | 168 (= Conder's graph) | negative above 168 (§4) |
| (4,7) | 840 (Bond–Delorme, Hafner, Loz) | 2,186 | 840 (= Bond–Delorme, A5 × Z7) | negative above 840 (§4) |
| (5,7) | 3110 (Loz) | 10,922 | – | rich and wide lift sweeps (orders 3112–3200): no solution; haar_gen3 sweep queued |
| (7,7), (9..16,7) | 23436 … 4022340 (DGQ) | | rebuilt 23436 = 3·GH(5) | §3.2 (polygon family saturated); Haar can't (tables 1.07–1.44 × the random ceiling) |
| **(3,8)** | 256 (DGQ) | 510 | **288** | **new record** (§2.0). Two pushes over orders 290–348 found nothing above 288 (best cost 10 at 320) |
| (4,8) | 2184 (Loz) | 6,560 | – | rich sweep (orders 2186–2260): no solution; wide sweep and haar_gen3 queued |
| **(5,8)** | 9234 (Loz) | 43,690 | **9,316** | **new record** (§2.0): Haar(Z137 ⋊₁₆ Z34) from the haar_gen3 sweep. The rich and wide lift sweeps (orders 9236–9500) found nothing; GH(3) + matching lifts reach only m = 6 (§3.3) |
| (10,11,12,14,16,8) | 1176480 … 36201060 (DGQ) | | – | §3.3: about 2.5× beyond random lifts of their family; μ = 57–733 at the table orders |
| (3,9) | 506 (Loz) | 1,022 | – | negative. 133 lift searches (rich sweep, orders 508–540; the wide sweep was cut short by the container restart): best cost 18 (n = 540). haar_gen3 sweep (N = 254–275): best cost 30. Field-affine 2+2 lifts are exhaustively negative (§4) |
| (4,9) | 4970 (Loz) | 19,682 | – | rich and wide lift sweeps (orders 4972–5100): no solution; haar_gen3 sweep queued |
| **(5,9)** | 27936 (Loz) | 174,762 | **28,842** | **new record** (§2.0); above it (N up to 14,700) best cost 2 |
| (3,10) | 800 (DGQ) | 2,046 | – | near misses at cost 2: n = 812 (2+2 base, Z29 ⋊ Z7) and n = 816 (3+3 base b3_3_0, Z17 ⋊ Z8). Both are **exhaustively** negative (8.3·10⁶ and 3.4·10⁸ assignments, best cost 2). Haar sweep (haar_gen3, N = 401–430): best cost 4. Exhaustive 2+2 scan over all rich groups, orders 804–860, running |
| **(4,10)** | 11748 (Loz) | 59,048 | **11,988** | **new record** (§2.0): Haar(Z333 ⋊₈₃ Z18) from the haar_gen3 sweep (N = 5,875–6,050). The rich and wide lift sweeps (orders 11750–12000) found nothing |
| **(5,10)** | 90068 (Loz) | 699,050 | **95,472** | **new record** (§2.0) |
| (15,10), (16,10) | 2.30·10⁹, 4.12·10⁹ (Loz) | | – | not run: N > 10⁹ (memory and 32-bit indices); the size law predicts +1 % at best |

## 3. Structured families: what was tried and why it stops

The green cells are the D = 5 cells with Δ ≥ 10, the D = 7 cells with Δ = 7 and Δ ≥ 9, and the D = 8 cells with Δ ≥ 10.
They sit above the Haar random-covering ceiling (research/frontier/SIZE_LAW.md §3.4), and the user's ranking makes them
the first priority: furthest below Moore, oldest records. I tested the structured families that could reach them.

**3.1 Girth obstruction (proved).** If the base B has girth g and Γ ≠ 1, every connected lift of B has diameter
≥ g − 1.
- *Proof.* Let x ~ y be joined by the edge e with voltage a. A walk from x to y of length < g − 1 closes, together
  with e, a closed walk of length < g. In a graph of girth g such a walk reduces to the trivial walk by cancelling
  backtracks, so its voltage is a. Hence (y, b) with b ≠ a is at distance ≥ g − 1 from (x, 1). ∎
- Consequences for lifts of bipartite Moore graphs with no extra edges:
  - PG(2,q) (g = 6) needs D ≥ 5;
  - GQ(q) (g = 8) needs D ≥ 7;
  - GH(q) (g = 12) needs D ≥ 11.
- So the (4,8) value 2184 = 3·|GH(3)| cannot be a Z3-cover of GH(3); annealing that lift gave cost 82,220.
- A GH(2)-based (3,10) lift (882 = 7·126) is impossible as well.

**3.2 The (2j+1)-fold polygon cover is saturated.** The construction GP + j matchings over Z_{2j+1} gives diameter
n + 1 for any matchings (LITERATURE.md §5). Searching for one more copy, with every voltage free:

| lift | would give | best cost (time) |
|---|---|---|
| W(3) + 1 matching, Z4 / Z2×Z2 (polygon voltages 0, matching free) | 320, D = 5 | 562 / 385 (40 s each) |
| W(3) + 1 matching, Z4, all voltages free | 320 | 360 (40 s) |
| W(5) + 1 matching, Z4, all voltages free | 1248, a (7,5) record | 6740 (40 s) |

So 2j+1 copies is where this family stops. A sketch of why, with voltage 0 on the polygon: a copy that is not
±(hop) can only be reached by two-hop walks. Each two-hop route covers at most the perp of one point, so a whole extra
copy needs about q+1 such routes, against about 4j² routes available. Not proved for general voltages.

**3.3 D = n+2 (the green D = 8 cells: m · |GH(q)| with m = 30–45).** Their construction is unpublished (LITERATURE.md
§5). Random-like voltages on GH(q) + j matchings fall far short:
- Small case GH(3) + 1 matching (Δ = 5, D = 8):
  - m = 6 (4368) solves in under a second;
  - m = 9 (6552) ends at cost 324–588 after 30 s;
  - m = 13 (9464, which would beat (5,8) = 9234) ends at cost 20,950.
- The coupon-collector estimate of SIZE_LAW.md §2.2, applied to the opposite-colour targets reached by walks of length
  ≤ 7:
  - GH(7) + 2 matchings (Δ = 10) has about 271 walks per base target pair;
  - random voltages should therefore reach m ≈ 271/ln(#targets/μ*) ≈ 12;
  - Delorme–Gómez–Quisquater reach m = 30.
- **The green D = 8 graphs are about 2.5× better than random lifts of their own family.** A random-voltage lift search
  will not beat them. This also matches the size law: random-like Haar graphs fall short there by 12–28 %.

**3.4 Lifts of GQ(q) alone at D = 7 = g − 1 (the boundary case of 3.1).**
- W(3) over Z10 (800) ends at cost 1018 and over Z11 (880, a (4,7) record) at cost 1362, after 60 s each.
- At D = g − 1 every edge needs all |Γ| voltages realized by the walks closing an 8-cycle with it. That is too few
  walks.

**3.5 Random model for small-base lifts (why bigger bases are not better at large N).**
- Take a lift with k base vertices and order n = kN. From each of the k sources, the binding targets are the k/2
  opposite-colour fibers.
- So the expected number of uncovered pairs at a given order n is (k/2)·n·e^(−2W/n), against n·e^(−2W/n) for a Haar
  graph (k = 2), with the same W.
- A random-like k-vertex lift therefore loses a factor ln(k/2)/ln(n/μ*) in order relative to Haar: about 10–15 % for
  k = 12.
- Larger bases can only win through structure. That is what the rebuilt records show: Conder's 168, A5 × Z7, and the
  polygon covers.

## 4. Honest negatives

- **(3,7), table 168 (Conder; our rebuild is isomorphic to it).**
  - 375 lift searches, 20 s each: Haar graphs and every connected cubic bipartite base on 2+2 … 7+7 vertices
    (complete lists up to 6+6, 200 random 7+7), generic groups, orders 170–200.
  - The best cost was 10 (n = 176, a 4+4 base over Z22). There is no graph above 168. This matches the Haar job
    (wave4: best cost 10).
- **(4,7), table 840 (Bond–Delorme = Haar(A5 × Z7), rebuilt exactly).** Haar graphs over the matrix-group products
  SL(2,3), S4, A4, A5, SL(2,5), S5, PSL(2,7), times cyclic or dihedral groups, N = 432–540, 2 seeds × 60 s: best costs
  18–56. The wave4 metacyclic runs reached cost 4.
- **Polygon covers beyond 2j+1 copies** (§3.2) and random-voltage lifts of GH(q) + matchings at D = 8 (§3.3): far from
  0.
- **Lifts of GQ(q) incidence graphs alone at D = 7** (§3.4): cost > 1000.
- **(5,10) above 91,728.**
  - SL(2,11) × Z35 (N = 46,200) and SL(2,13) × Z22 (N = 48,048) were at cost 4–6 after about 450 s of wall time.
    The machine was oversubscribed.
  - Both were killed by a container restart (18:52) before finishing. They are re-queued at the end of
    runs/haar_cells.sh.
- **(3,9) with field-affine groups on the 2+2 cubic base** (the (3,8) recipe). Exhaustive over all voltage
  assignments, no solutions:
  - Z3² ⋊ Z16 (576 vertices), four actions: best costs 52–78;
  - Z2³ ⋊ Z21 (672): best costs 76–108.
- **(3,10) near misses, exhaustively closed.** These are complete searches over all gauge-fixed assignments, so "no
  solution" is definitive for the stated base and group:
  - 2+2 base over Z29 ⋊ Z7 at 812;
  - 3+3 base b3_3_0 over Z17 ⋊ Z8 at 816;
  - 2+2 base over Z3² ⋊ Z24 at 864, six actions (best costs 4–50).
- **Cyclic K3,3 lifts at (3,8).** Exhaustive: Z43 (258) is the only order with solutions in N = 43…60. For
  N = 44–60 the best costs are 10, 16, 22, 26, 28, …, 130, rising with N.
