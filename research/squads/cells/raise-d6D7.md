# Cell (Δ, D) = (6, 7): raise job "raise2-6-7" (round 2)

Branch `claude/raise-d6d7-round-2-v09d6t`. Record at the start of round 2: **8,880** vertices (Haar graph of
SL(2,5) × Z37, N = 4,440, orbit method k = 3, m = 2, f = 0; `research/frontier/sols/d6D7_sl_5_37_orb3f0_s2.txt`).
Table 8,310. Bipartite Moore bound 39,062. A new record needs N ≥ 4,441 (2N ≥ 8,882).

**Result of round 2: no record. The record stays 8,880.** Every orbit-symmetric route that reaches N ≥ 4,441 has
now been measured, and none of them has a solution. Details and the reasons are below. Scripts and logs are in
`research/squads/cells/raise-d6D7-r2/`.

## Round 1 (branch claude/raise-d6d7-record-0em0u0), read first

Orbit annealing (k = 3, m = 2, f = 0; and f = 3, m = 1) on sl 9×7, sl 5×43, psl 11×7, psl 9×13, psl 7×31, psl 5×79,
sl 17, pgl 17, plus small-Q groups. Each group stalled at one floor across seeds and budgets (14 to 72 uncovered).
Round 1's next steps: diagnose the floor, voltage lifts, odd-order groups. Round 2 did the first of these as an
exhaustive scan and tried two other routes.

## Round 2, step 1: exhaustive scan of the orbit space (RESULTS.md)

Orbit space for k = 3, m = 2, f = 0: all unions of two free α-orbits, about N²/18 ≈ 1e6 sets for N ≈ 4,500.
haar_sym's `RANDORB` evaluates a sample in ~5 µs (~60 µs for the small-Q groups, which use the slow generic evaluator).
Sampling 1.5·10⁷ times covers every orbit pair with probability > 1 − 10⁻⁵, so the minimum over samples is the minimum
over the space. Calibration: on the record group the same run finds 147 zero-cost sets in the first 200,000 samples,
so zeros are not rare when they exist.

Every group in the screen (`research/structured/tools/orb_screen.py 6 7 4441 5300 "3 2 0" --list`, 17 groups, both
cube roots of unity where n is prime) has minimum > 0:

| group | N | min uncovered | round 1 annealing floor |
|---|---|---|---|
| psl 11 × 7 | 4,620 | **14** | 14 |
| psl 7 × 31 | 5,208 | 24 | 24 |
| psl 9 × 13 | 4,680 | 25 | 25 |
| sl 17 | 4,896 | 28 | 28 |
| pgl 5 × 43 | 5,160 | 46 | (not run) |
| sl 9 × 7 | 5,040 | 48 | 48 |
| pgl 9 × 7 | 5,040 | 52 | (not run) |
| psl 5 × 79 (= A5 × Z79) | 4,740 | 54 | 54 |
| sl 5 × 43 | 5,160 | 72 | 72 |
| small-Q groups (psl/sl/pgl 3 × Z_n, prod psl 3 …) | 4,464 to 5,208 | 66 to 5,952 | — |

The sampled minima equal the round-1 annealing floors for every group that both rounds ran. So those floors are not
search failures: the orbit spaces contain no solution. Note on coverage: the small-Q groups used 2·10⁶ samples
(~80 % of their space). Their minima are far above zero, so the gap does not change the verdict.

Limitation: the inner part of α is one conjugacy class of order-3 elements per group (for PSL/SL(2,p) I believe these
form one class, but I did not verify this group by group). The two scalings r, r² on Z_n were both run.

## Round 2, step 2: second orbit type, f = 3, m = 1 (ORBIT = "3 1 3")

S = {e, t₁, t₂} ∪ one α-orbit, with t₁, t₂ in Fix(α). The space is ~10⁴ sets, so 3·10⁶ samples is effectively exhaustive.
Minimum uncovered: sl 5×37 (control, the record group) 924; psl 11×7 186; sl 9×7 96 (best); psl 9×13 258; sl 17 144;
sl 5×43 1,686; pgl 5×43 972. No solution.

## Round 2, step 3: involution orbits, ORBIT = "2 3 0" (sampled, not exhaustive)

S = three α-orbits of size 2, α an involution. The space is ~10⁹, so 3·10⁶ samples is a sample, not an exhaustive
scan. Minimum over samples: sl 5×37 198; psl 11×7 38. These are far above zero. The structure notes (STRUCTURE §2.1)
give the reason: for an involution α, words u with α(u) = u⁻¹ collide at every BFS level. This is weak evidence, but
it does not point to a route.

## Why the other routes were not run

- **Hexagon-family construction at q = 4 (Δ = q + 2).** The (7,7)…(16,7) records come from generalized hexagons with
  hubs and R-surgeries. At (6,7) the hexagon base is three copies of the incidence graph of H(4): 3 × 2,730 = 8,190
  vertices, below 8,880. The surgery gains in the family are 0.5–0.7 % of the base at q = 5 and 7 (record vs base),
  and it would need 8.4 % here. So this route cannot pass 8,880 at this degree. (This is a size estimate from the
  family's own numbers, not a full proof.)
- **Metacyclic groups with an order-3 automorphism.** Any α of order 3 on Z_m ⋊ Z_k acts trivially on the abelian
  quotient Z_k unless 3 | k, and then it still acts trivially on a Z_3 quotient. Orbit-symmetric S then has collisions,
  so the metacyclic family is excluded from the orbit method.
- **Random (non-orbit) annealing above N = 4,440.** μ = N·exp(−19,531/N) is 54.6 at N = 4,440 and about 67 at 4,620.
  Random annealing solved μ ≈ 41 on the 4,220 metacyclic group in an hour-scale job (round 1). It cannot reach μ ≈ 55.

## Where this leaves the cell

- Among the orbit-symmetric routes that the existing tools support, every group of order 4,441 to 5,300 has no solution.
  The record group sits exactly at the edge (N = 4,440). The next candidate groups are ≥ 4,620 and all have minima ≥ 14.
- The first-moment count for k = 3, m = 2 gives about N²/18 · e^(−μ/3) ≈ 10⁻² at N = 4,440 and 10⁻⁵ at N = 4,700. The record
  exists, so the count underestimates; but nothing in the window beats it.
- Stop criterion met: the cell will not move further with these methods. The untested items (voltage lifts over other
  bases, other α classes, group families the screen does not list) are the only open leads, listed next.

## Open leads, if the coordinator wants more compute

1. Verify that psl 11×7, psl 7×31 and sl 17 have a single class of order-3 elements under conjugation (the one assumption
   the screen relies on). Then the orbit exhaustion is complete for these groups.
2. Voltage lifts of a small bipartite base (research/lifts/, route-chart lifts) with non-cyclic voltage groups of
   order 4,441 to 5,300. Not run.
3. Groups outside orb_screen's families (csl, tpgl, larger central products) in the same window.
