# raise-d4D10: notes (Haiku worker, job "raise3-4-10", round 3)

Goal: beat 12,416 at (Δ, D) = (4, 10). Table 11,748 (Loz); Moore bipartite 59,048.
Record: Haar graph of Z97 ⋊19 Z64, N = 6208, n = 12,416 (research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt).

## Where rounds 1 and 2 stopped (branches claude/raise-d4d10-haar-l3s318 and claude/raise-d4d10-haar-round2-07skbp)
- About 150 Haar anneals (300 s, plus 1200–2400 s re-anneals) over N = 6209–6560, metacyclic split groups × Z_n. No solve.
- Closest: N = 6394 meta 139 46 6 1, meta 139 23 6 2, meta 278 23 45 1 at cost 1 (2400 s, seeds 2–3).
- Round 2 left three untried routes: (a) longer runs at N = 6394; (b) non-Haar lift.c at n > 12,416 (round 1's K_{4,4}
  lifts were at cost ~1000 after 63 s, so this is far off); (c) group families outside the haar_gen3 grammar.

## Round 3: what this round tried
Two families that the grammar could not reach before, and one check that closed a route.

1. **Orbit-symmetric S with k = 3 (ORBIT="3 1 1" in haar_sym): closed, no solve.** S = {e} ∪ one α-orbit of size 3.
   RANDORB (20,000 random orbits per group, which covers the whole space of ~N/3 orbits) on every round-2 candidate
   in 6209–6480 (17,627 specs; the sweep was stopped once the picture was clear, and the non-metacyclic specs were rerun
   in full). Best exhaustive minimum: psl 7 × Z37 (N = 6216) at 18 uncovered; sl 5 × Z52 (N = 6240) at 186; every
   metacyclic group ≥ 306. Cost 0 needs 0. This matches STRUCTURE.md's "one orbit is too few" lesson for Δ = 4.
   Scripts: research/squads/cells/raise-d4D10-round3/tools/orb_screen.sh. Logs: .../logs/scr_k3f1_nonmeta.tsv.

2. **Non-split metacyclic groups (new family): screen and anneal.** Groups Z_m . Z_k with b a b⁻¹ = a^r and b^k = a^s,
   s ≠ 0 (not split, so not in the meta grammar). Checked: with s = 0 the new code reproduces haar_gen3's split meta
   screen exactly (same min/p10/median). Tools: research/squads/cells/raise-d4D10-round3/tools/haar_nm.c (haar_gen3 plus
   the G_NMETA type, group axioms checked at parse time), gen_nmeta.py (candidate list; normal form s = divisor of m,
   non-split iff gcd(S_r, m) ∤ s), screen_nm.py (RANDSAMPLE 200, round-2 rule).
   Screen: 23,377 candidates in N = 6209–6400. Best min 9–13 (e.g. 6328 nmeta 226 28 117 113 1: min 9, median 293),
   comparable to the best split groups (min 10–13). Log: logs/screen_nm_6209_6400.tsv.

   Batch 1 (300 s, seed 1, 12 specs): the four N = 6328 specs nmeta 226 28 {99,105,169,173} 113 reach cost 2; the
   others (6216 518 12 {177,487} 259, 6223 889 7 8 127, 452 14 143 226) reach cost 5–7. Batch 2 (12 more, N = 6216–6384)
   was cancelled in favour of the long runs below. Log: logs/anneal1_summary.tsv.

3. **Long runs at N = 6394 (round 2's lead (a)): no solve.** Four runs of 3600 s each (haar_gen3, split groups, seeds 4–5):
   meta 139 46 6 1 (seeds 4, 5), meta 139 23 6 2 (seed 4), meta 278 23 45 1 (seed 4). Every run ends at best cost 1
   (about 4.3e8 evaluations each). Log: logs/long6394_summary.tsv.

4. **Wider non-split sweep (300 s anneals, seed 1): no solve.**
   - Batch 3: the next 40 non-split candidates by screen score (N = 6216–6384). Best cost 2 (8 specs, all N = 6328 or
     6223/6216 in the 226·28 / 452·14 families); the rest 4–7. Log: logs/anneal3_summary.tsv.
   - Batch 4: screen of N = 6401–6480 (9,523 candidates; best screen N = 6435 nmeta 429 15 334 143). Eight anneals:
     best cost 8 to 300. This window is weaker than 6209–6400. Logs: logs/screen_nm_6401_6480.tsv, logs/anneal4_summary.tsv.
   - Totals for the non-split family: 23,377 + 9,523 screened; 24 anneals of 300 s plus the 6328/6394 leads above.

## Stop decision (round 3, 04:00 UTC, about 2.7 h of the 6 h budget)
Stopping, because the cell did not move on any route tried this round, and the remaining routes are low-yield:
- The record's order-6208 group has no order-3 automorphisms, and the k = 3 orbit family is exhaustively below 0 (best 18).
- The non-split metacyclic family screens as well as the split one, but its anneals floor at cost 2 at 6328 (a 300 s
  pattern seen across 24 specs) and at 6394 the best ~ cost 1 persists over 3600 s runs, as in round 2.
- Stopping only leaves the compute-heavy items below; they are for the coordinator to choose.

Untried, for the coordinator (in order of my estimate):
  (a) Non-metacyclic groups beyond the haar_gen3 grammar: Z_p^2 ⋊ Z_k with a non-diagonal action, and nonsplit products.
      The 37 sl/psl/pgl/agl1 specs in 6209–6480 were screened with the k = 3 orbit rule only, and never annealed with
      plain (non-orbit) S beyond psl 7 × Z37 (round 2, 300 s, best cost 9).
  (b) More seeds on the N = 6394 cost-1 specs (3600 s each; four done this round, all cost 1).
  (c) Non-Haar lift.c at n > 12,416 (round 1 K_{4,4}: cost ~1000 after 63 s, so far off).

## Status (round 3, as of 03:00 UTC)
- Total this round: 4 long runs (3600 s), 4 + 4 non-split anneals (300 s), and the k=3 orbit screen (17,627 candidates,
  exhaustive for the orbit space of each candidate). No solve; nothing saved to research/frontier/sols/.
- Verification pipeline is checked (for any future hit): haar_nm finds the solution, tools/build_haar_nm.py gives VALID
  (degree 4, bipartite, diameter from both sides), and research/lifts/coordinator_check/apsp.c gives the all-pairs
  diameter. Tested on a small nmeta case (nmeta 6 4 5 3 1, d=4 D=6: VALID, diameter 5).
