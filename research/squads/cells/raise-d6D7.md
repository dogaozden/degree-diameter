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

## Round 3, raise3-6-7 (branch claude/raise-d6d7-round-3-dhhj7z)

**Result: no record. The record stays 8,880** (sl 5 × Z37, N = 4,440). No sample with cost 0 at N ≥ 4,441 in any screen below.
Scripts, job lists and logs: `raise-d6D7-r3/` (see its README). Round 2's notes are above, unchanged.

Method check first: haar_sym with ORBIT "3 2 0" on sl 5 × Z37 (the record group) returns cost 0 within 2·10⁵ samples, so the
screen can see a solution when one exists.

Round 3 covered what round 2 did not: orbit orders 2, 4, 5, 6 (round 2 had only 2 and 3), metacyclic groups, and Heisenberg groups.

| family / α | jobs, samples | smallest minimum (uncovered) | notes |
|---|---|---|---|
| metacyclic Z_m ⋊_r Z_K, K ≥ 12, gcd(r−1,m)=1, α = (u a, j) of order 2 (`2 3 0`) | 171, 10⁵ | 44 | the first pass, stopped after 171 of 3,145 jobs (too slow) |
| metacyclic, α of order 3 (`3 2 0`), 4 (`4 1 2`), 5 (`5 1 1`), 6 (`6 1 0`) | 2,091, 3·10⁴ | **400** | every orbit space here is small, so the minimum is essentially exact |
| psl 9×13, psl 7×29, sl 5×41, pgl 5×41, sl 4×85, psl 5×85, pgl 4×85, sl 17, pgl 17, α of order 4 (`4 1 2`) | 9, 10⁶ | 70 (pgl 17) | exact-size spaces; psl 9×13 192, psl 7×29 276, sl 5×41 2,668 |
| α of order 5 (`5 1 1`): sl 5×41, pgl 5×41 | 2, 10⁶ | 85 (pgl 5×41) | one orbit plus one fixed element: about N choices, so exhaustive |
| α of order 6 (`6 1 0`): psl 11×7 | 1, 10⁶ | 166 | psl 9×13, sl 9×7, sl 17: no conjugation of order 6 |
| α of order 2 (`2 2 2`, `2 3 0`, `2 1 4`): psl 11×7, psl 9×13, sl 5×43, sl 5×41, heis 17 | 5, 10⁶ | 58 (psl 11×7, `2 2 2`) | sampled, not exhaustive |
| Heisenberg H(q) × Z_n (heis 5×37, 5×41, 7×13, 17): orbit orders 2, 3, 4 | 6 | 1,296 (heis 7×13, `3 2 0`) | four jobs refused by haar_sym ("not enough fixed elements") |

Reading. The best of every new family is far from zero, and the k = 3 psl 11×7 minimum of 14 from round 2 is still the closest
any orbit space has come. Metacyclic groups are out for orbit orders 3 to 6. The order-4 and order-5 spaces at N ≈ 4,700–5,100
are exhausted, with minima 70 to 276 (k = 4) and 85 to 96 (k = 5) uncovered. Heisenberg groups have too few fixed elements for these
α types, and the one that ran was poor (1,296 or more).

Why these numbers say no, in brief. The first-moment count (round 2) gives about N²/18 · e^(−μ/3) orbit sets at k = 3. At k = 4
and k = 5 the spaces are smaller (about N·|Fix| and N sets), and the same μ_eff ≈ 18 applies, so the expected number of solutions
is smaller still. This is a heuristic; it does not rule out a structured solution. It says the orbit method has no slack left
in the N = 4,441 to 5,300 window at this degree.

Open leads, none tried this round:
1. **Voltage lifts with two orbits per side** (base 2 + 2, multiplicities [[a, 6−a], [6−a, a]], voltage group G of order
   2,221 to 2,650, N = 4|G| ≥ 8,884). This is the only route here that could beat 8,880 without a single cyclic orbit structure.
   Needs a new evaluator (4 BFS roots instead of 2). Not built this round.
2. Groups outside orb_screen's families and haar_sym's group types (central products, tpgl, Z_n ⋊ Q).
3. Verify the single-class assumption for order-3 elements in PSL(2,q). It holds for PSL(2,p) (Aut = PGL(2,p), and order-3
   elements of PGL lie in PSL), so the only open part is composite q.

Stop criterion. Round 3 has measured every orbit-order and metacyclic family the tools support in the window. Nothing reached zero.
The cell is not expected to move further with the orbit or metacyclic-orbit methods. The next step is lead 1, which is a new
search code, a bigger job than these screens.
