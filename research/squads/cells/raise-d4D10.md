# raise-d4D10: notes (Haiku worker, job "raise2-4-10", round 2)

Goal: beat 12,416 at (Δ, D) = (4, 10). Table 11,748 (Loz); Moore bipartite 59,048.
Record: Haar graph of Z97 ⋊19 Z64, N = 6208, n = 12,416 (voltage-lifts branch, research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt).

## Round 1 (branch claude/raise-d4d10-haar-l3s318; its notes are at that branch's research/squads/cells/raise-d4D10.md)
- About 150 anneals of 300 s over N = 6209–6560 (metacyclic, n = 1) plus 4 long re-anneals. No solve.
- Closest: N = 6216 meta 259 24 97 (cost 1, stalled to 2400 s); N = 6394 meta 278 23 45 and meta 139 46 6 (cost 1, one 300 s seed each).
- Untried by round 1, and taken up here: non-metabelian families; and metacyclic × Z_n with n ≥ 2 (see below).

## Round 2 (this branch)
Gap found: research/frontier/sizelaw/small_cands.py only generates metacyclic Z_m ⋊ Z_k with n = 1. The product
metacyclic × Z_n (n ≥ 2, order m·k·n) is a haar_gen3 family ("meta m k r n") that no earlier sweep screened.
- Candidates for N = 6209–6330: 5,227 meta × Z_n (n ≥ 2) + 2,571 metacyclic (n = 1) + 37 matrix/product families (cands_gen.py).
  Tools in tools/: gen_meta_xn.py (the new family), screen_all.py (RANDSAMPLE 200, same call as haar_cell.py), rank.py (same
  score as haar_cell.py: (p10 + median) / mu(N)). screen_6209_6330.tsv holds all 7,835 screens.
- Record screen score (N = 6208): 4.03. Candidates scoring below 4 in the window: about 40.
- Batch 1 (queue1.txt): top 40 overall plus 20 more with n ≥ 2, 300 s each, seed 1, 4 cores, THREADS=1, nice.
  Round-1 near misses excluded (N = 6216 meta 259 24 97, 6270 meta 209 30 26, 6270 meta 418 15 49, 6275 meta 251 25 4,
  6321 meta 301 21 23).

## Batch 1 result (60 anneals, 300 s, seed 1, N = 6216–6330 and the new family)
- No solve. 25 of the 60 were metacyclic × Z_n (n ≥ 2). Cost distribution: 2 at cost 2 (min), 1 at 3, 6 at 4, 4 at 5,
  9 at 6, 9 at 7, 6 at 8, 4 at 9, the rest higher.
- Best: N = 6270 meta 209 15 26 2 (cost 2, new family); N = 6328 meta 113 56 2 1 (cost 2); N = 6321 meta 301 21 4 1 (cost 3).
- Log: logs/q1.tsv. The new family is not clearly better than the metacyclic n = 1 ones on this screen-and-anneal budget.
- Monitor note: a watch loop with `pgrep -f "haar_gen3 4 10"` matches its own command line and never ends. Use a line count on the log.

## Batch 2 (started 15:49 UTC): 1200 s re-anneals, seed 2, of the cost-2/3 near misses and the round-1 cost-1 N = 6394 candidate
  meta 209 15 26 2 (6270); meta 113 56 2 1 (6328); meta 301 21 4 1 (6321); meta 278 23 45 1 (6394). Log: logs/q2.tsv.

## Batch 2 result (1200 s, seed 2): no solve
- 6270 meta 209 15 26 2: cost 2. 6328 meta 113 56 2 1: cost 2. 6321 meta 301 21 4 1: cost 3. 6394 meta 278 23 45 1: cost 1.

## Batch 3 (screen N = 6331–6420: 5,613 candidates; top 40 annealed 300 s, seed 1): no solve
- Best: N = 6394 meta 139 46 6 1 (cost 1) and N = 6394 meta 139 23 6 2 (cost 1). The rest are cost 4 and up.
- Order 6394 now has three specs stuck at cost 1 (meta 278 23 45 1 and the two above). This order is the best lead.
- Log: logs/q3.tsv; screen: screen_6331_6420.tsv; queue: queue3.txt.

## Batch 4 (started 17:00 UTC): 2400 s, seeds 2–3, the N = 6394 cost-1 specs
  meta 139 46 6 1 (seeds 2, 3); meta 139 23 6 2 (seed 2); meta 278 23 45 1 (seed 3). Log: logs/q4.tsv.

## Batch 4 result (2400 s, seeds 2–3, N = 6394): no solve
- meta 139 46 6 1 (seeds 2 and 3): cost 1. meta 139 23 6 2 (seed 2): cost 1. meta 278 23 45 1 (seed 3): cost 1.
- Three specs at order 6394 stall at cost 1 across 300–2400 s runs and several seeds.

## Batch 5 (screen N = 6421–6480: 4179 candidates; top 40 annealed 300 s, seed 1): no solve
- Best cost 8. Nothing close. Log: logs/q5.tsv; screen: screen_6421_6480.tsv.

## Status and stop decision (round 2, about 4 h of the 6 h budget used)
- Total: 148 anneals (60 + 4 + 40 + 4 + 40) over N = 6216–6480. No solve. Every record file is
  unchanged; nothing was saved to research/frontier/sols/.
- Why I stopped:
  - The new family (metacyclic × Z_n, n ≥ 2) was screened at full size (7,835 specs in 6209–6330 and 5,613 in 6331–6420),
    and the best of it reached cost 2 (6270) and cost 1 (6394). It did not beat the metacyclic n = 1 candidates by a margin.
  - Order 6394 has three specs stuck at cost 1 across 300–2400 s runs and several seeds; the window above 6394 is at cost 8 or more.
  - The window 6421–6480 screens worse and its top 40 are far off.
- The cell is not moving further with these methods (Haar anneal over the existing families, with haar_gen3 and the
  current screen score).
- Untried, for the coordinator (in order of my estimate):
  (a) longer runs (≥ 3600 s, 4 seeds) at N = 6394 for the three cost-1 specs, or any solve there would be a record (n = 12,788);
  (b) non-Haar: lift.c with a 2+2 or dipole-plus-matching base at n > 12,416 (round 1 and round 2 did not run it there);
  (c) group families outside the haar_gen3 grammar: Z_p² ⋊ Z_k (affine, Heisenberg) and non-split products.
- No solve, so nothing needs verifying. Scripts and logs are in research/squads/cells/raise-d4D10-round2/.
