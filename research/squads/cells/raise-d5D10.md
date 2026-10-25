# Cell (Δ, D) = (5, 10): job raise-5-10

Haar worker session `claude/raise-d5d10-haar-otvuvl`, 2026-10-25 (Haiku 5.5, cloud). Goal: beat the current record
**95,472** vertices (group order N = 47,736, Haar graph of Z1989 ⋊₄₆₁ Z24, connection set (0,0), (826,18), (423,7),
(1635,11), (993,10); found by the voltage-lifts session on `claude/voltage-lifts-search-6lfotq`). Table 90,068 (Loz).
Moore bound 699,050. Bipartite Haar graph of order N has 2N vertices, so beating 95,472 means group order N > 47,736.

## Where the record came from (read from `claude/voltage-lifts-search-6lfotq`, research/lifts/RESULTS.md)

- Random-S annealing on metacyclic groups, N = 47,501–48,500 (36,804 screened candidates). Best cost 1 at N = 47,766
  (Z1257 ⋊₄₇ Z38) and N = 48,006 (Z1143 ⋊ Z42). Cost 2 at 47,754 and 48,455, cost 3 at 48,200.
- The voltage session did not sweep non-metacyclic matrix products in this window.

## Size law at this cell (SIZE_LAW.md, W = Δ g (Δ−1)^(D−2) with D even)

- W = 5 · 4⁸ · 16/15 = 349,525. Poisson mean μ = N e^(−W/N): μ = 31.6 at N = 47,748, 33 at 48,000, 37 at 48,660, 40 at 49,140.
- The fitted wall ln μ* = 4.34 − 0.123 ln N gives μ* ≈ 20 at N = 47.7k. The record already sits at μ ≈ 31.5, above that
  wall, so this cell is not a random-like-law cell; group structure is what makes the record possible.

## Tool checks (this session)

- `haar_gen3` on the record group itself (`meta 1989 24 461 1`, seed 1, 300 s, 3.3M evals, ~11k evals/s): best 2.
  Random-S annealing needs far more than one short run even on the known-good group.
- **Abelian cyclic factors kill coverage at this order.** `psl 5 × Z_n` (A5 × Z_n): start cost 352 at n = 211 (N = 12,660),
  177 at n = 401, and 4,584–43,298 at n = 811 (N = 48,660, six seeds, best ~2,000 after 1 s). So products with a large
  cyclic factor are structurally bad. Keep cyclic factors small, or use groups with small abelianization.
- **Orbit-symmetric S (k = 5, f = 0) is not viable here.** An automorphism of order 5 acting on the cyclic factor needs a
  prime p ≡ 1 (mod 5), i.e. a large cyclic factor, which the previous bullet rules out. Conjugation-only α on
  PSL/SL(2,q) × Z_n has |C_G(α)| = |C_H(g)| · n, about 60–140 fixed points, far above the e^(−λ/5) budget.

## Screen 1: matrix products × small cyclic factor (random S, haar_gen3, 40 s, seed 1)

Start cost is the uncovered count of one random S; best is after 40 s. Orders are all in (47,736, 49,500].

| group | N | μ | start | best (40 s) |
|---|---|---|---|---|
| psl 19 × Z14 | 47,880 | 32.3 | 97 | 5 |
| sl 19 × Z7 | 47,880 | 32.3 | 1,644 | 5 |
| pgl 19 × Z7 | 47,880 | 32.3 | 89 | 6 |
| psl 29 × Z4 | 48,720 | 37.3 | 65 | 9 |
| sl 29 × Z2 | 48,720 | 37.3 | 1,182 | 4 |
| pgl 29 × Z2 | 48,720 | 37.3 | 856 | 17 |
| psl 23 × Z8 | 48,576 | 36.4 | 69 | 6 |
| sl 23 × Z4 | 48,576 | 36.4 | 129 | 6 |
| pgl 23 × Z4 | 48,576 | 36.4 | 149 | 14 |
| sl 16 × Z12 | 48,960 | 38.9 | 190 | 10 |
| psl 17 × Z20 | 48,960 | 38.9 | 2,159 | 9 |
| sl 17 × Z10 | 48,960 | 38.9 | 219 | 9 |
| pgl 17 × Z10 | 48,960 | 38.9 | 24,480 | 12 |
| psl 27 × Z5 | 49,140 | 40.0 | 226 | 7 |
| sl 13 × Z22 | 48,048 | 33.3 | 86 | 10 |
| pgl 13 × Z22 | 48,048 | 33.3 | 81 | 9 |
| psl 13 × Z44 | 48,048 | 33.3 | 73 | 9 |
| psl 11 × Z73 | 48,180 | 34.1 | 326 | 16 |
| sl 11 × Z37 | 48,840 | 38.1 | 246 | 12 |
| psl 11 × Z74 | 48,840 | 38.1 | 383 | 18 |
| psl 9 × Z133 | 47,880 | 32.3 | 1,265 | 21 |
| psl 8 × Z96 | 48,384 | 35.3 | 5,773 | 32 |
| psl 7 × Z285 | 47,880 | 32.3 | 3,736 | 45 |
| sl 5 × Z399 | 47,880 | 32.3 | 9,057 | 451 |

Reading: large cyclic factors (≥ 73 or ≥ 96) and SL with an even central Z2 start high and stay high. The best
short-run candidates are psl 19 × Z14, sl 29 × Z2, psl 23 × Z8, pgl 19 × Z7 and psl 29 × Z4. Single 40 s runs are noisy.

Reference point from the voltage logs (`claude/voltage-lifts-search-6lfotq`): sl 13 × Z21 (N = 45,864, μ ≈ 22)
reached cost 0 in 204,761 evaluations (9 s). sl 11 × Z35 (N = 46,200) stalled at cost 4 after 36.7M evaluations.

## Batch A: 30 min per run, seed 2, four cores (started 07:46 UTC)

| group | N | μ | best after 30 min | evals |
|---|---|---|---|---|
| psl 19 × Z14 | 47,880 | 32.3 | 4 | 28.0M |
| sl 29 × Z2 | 48,720 | 37.3 | 2 | 24.9M |
| psl 23 × Z8 | 48,576 | 36.4 | 6 | 20.9M |
| pgl 19 × Z7 | 47,880 | 32.3 | 4 | 27.0M |

None solved. sl 29 × Z2 is the closest (cost 2, μ = 37.3).

## Batch B (started 08:19 UTC, 30 min each)

sl 29 × Z2 with seeds 3 and 4, plus the two voltage-session metacyclic leads that stopped at cost 1 there:
`meta 1257 38 47` (N = 47,766, μ 31.7) and `meta 1143 42 47` (N = 48,006, μ 33.1). Both group specs were checked
(gcd(r, m) = 1 and r^k ≡ 1 mod m).

## Batch B results (30 min each, finished 09:05 UTC)

| group | N | μ | best | evals |
|---|---|---|---|---|
| sl 29 × Z2, seed 3 | 48,720 | 37.3 | 3 | 25.6M |
| sl 29 × Z2, seed 4 | 48,720 | 37.3 | 2 | 25.6M |
| meta 1257 38 47 (seed 1) | 47,766 | 31.7 | 1 | 22.4M |
| meta 1143 42 47 (seed 1) | 48,006 | 33.1 | 1 | 24.6M |

Still none solved. The two metacyclic leads reproduce cost 1, as the voltage session found, and stall there.

## Batch D: orbit-symmetric S (k = 3, f = 2) on the top groups, 5 min each (10:05–10:16 UTC)

ORBIT="3 1 2": S = {e, β} ∪ {x, αx, α²x} with β fixed by α, α = conj by an order-3 element × (z ↦ r z).

| group | N | μ | fixed points | best | evals |
|---|---|---|---|---|---|
| **pgl 19 × Z7** | 47,880 | 32.3 | 17 | **0 (solved in 289 evals)** | 289 |
| psl 19 × Z14 | 47,880 | 32.3 | 17 | 8 | 5.0M |
| sl 29 × Z2 | 48,720 | 37.3 | 59 | 60 | 4.0M |
| psl 23 × Z8 | 48,576 | 36.4 | 95 | 121 | 6.1M |

Random S on the same groups (batches A–C) stalled at cost 1–2 with 20–28M evaluations. The orbit form solves
pgl 19 × Z7 at once, so the orbit route is much more efficient here, but it is group-dependent.

## NEW RECORD: (5,10) 95,760 vertices (was 95,472)

- Group PGL(2,19) × Z7, N = 47,880, d = 5, D = 10, S = {e, β} ∪ α-orbit (α = conjugation by an order-3 element × z ↦ 2z).
- File: `research/frontier/sols/d5D10_n95760_haar_pgl19x7_orb3f2.sol` (header `5 10 pgl 19 n 7 N 47880`).
- Verification, two independent checkers:
  - `research/frontier/build_haar2.py`: VALID, n = 95,760, 239,400 edges, 5-regular, bipartite, ecc from A and B = 10.
    Edge list sha256 `89813309f58e0bba9693dd07b0aaccb283846d6a29a6bb23cc80242148593b5a`.
  - all-pairs BFS (`research/lifts/apsp.c` from the voltage branch, no symmetry assumed): diameter 10, 95,760 sources,
    connected, bipartite, 5-regular, no repeated edges or loops.

## Batch E: orbit screen (k = 3, f = 2), 60 s per group, 22 groups with N ≥ 47,880

Best cost after 60 s (fixed points in brackets). Only the orbit route is shown; random-S results are in batch A–C.

| group | N | best | group | N | best |
|---|---|---|---|---|---|
| sl 19 × Z7 | 47,880 | 3 [17] | psl 37 × Z2 | 50,616 | 69 [35] |
| pgl 11 × Z37 | 48,840 | 28 [11] | sl 37 × Z1 | 50,616 | 46 [35] |
| psl 11 × Z74 | 48,840 | 51 [11] | pgl 37 × Z1 | 50,616 | 66 [35] |
| sl 11 × Z37 | 48,840 | 71 [11] | sl 8 × Z95 | 47,880 | 58 [44] |
| psl 29 × Z4 | 48,720 | 79 [59] | psl 13 × Z44, sl 13 × Z22, pgl 13 × Z22 | 48,048 | 463–4,701 [263] |
| pgl 29 × Z2 | 48,720 | 96 [59] | psl 17 × Z20, sl 16 × Z12 and the other 17s | 48,960 | 206–378 [179] |
| sl 23 × Z4 | 48,576 | 112 [95] | psl 27 × Z5 | 49,140 | 101 [134] |
| pgl 23 × Z4 | 48,576 | 136 [95] | pgl 9 × Z67, sl 9 × Z67 | 48,240 | 205–330 [8–17] |

Only the groups with few fixed points (pgl 11 × Z37, sl 11 × Z37, psl 11 × Z74 with 11 each) are close enough to
spend 30 min on (batch F).

## Batch F (started 10:44 UTC, 30 min each, orbit k = 3, f = 2)

pgl 11 × Z37 (seeds 2 and 3), sl 11 × Z37 (seed 2), psl 11 × Z74 (seed 2).

## Status

Record raised to 95,760 (pgl 19 × Z7, orbit k = 3, f = 2). Next: scan the orbit route over more groups at N > 47,880.

