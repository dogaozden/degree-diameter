# Voltage lifts: results (voltage-lifts job, 2026-10-23)

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

### 2.1 New record: (3,8) = 258 (table 256)

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

### 2.2 Per-cell campaign results

(filled in from runs/*.tsv as the campaigns finish)

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

(in progress)
