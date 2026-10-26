# Cell (Δ, D) = (15, 9): raise job raise-15-9, round 3 (branch claude/raise-d15d9-record-r3-u6folv)

**RECORD: (15,9) raised to 208,483,200 vertices** (from 208,029,120). Group prod SL(2,5) × SL(2,19) × Z127, |G| = 104,241,600,
15-regular, diameter 9, orbit search k = 3, m = 5, f = 0, ORBW = 5, seed 52 (wave 2, 3,424 s, 8,385 evals).
File: research/frontier/sols/d15D9_prod_sl_5_sl_19_127_orb3f0_s52.txt (sha256 2ec69cb54c41c25367a0c2baa57040cf2ac63cd3f92bbeea9215f7a3dc234fc6).
Checks: haar_sym's full diameter check OK, before and after normalising s₀ = e. Independent: research/structured/tools/haarcheck_prod.c
(VALID, both sides reach all 104,241,600 vertices within 9 from (e,A) and (e,B), 15 distinct generators, 3.5 min).
build_haar2.py is not used above 20M vertices; haarcheck_prod is the product checker for this family.


Goal (original): beat our record 208,029,120 vertices, i.e. a Haar graph with |G| ≥ 104,014,561 (2|G| vertices, 15-regular,
diameter 9). Table value 168,016,334. Current record: SL(2,79) × Z211, |G| = 104,014,560, orbit search k = 3, m = 5,
f = 0 (research/frontier/sols/d15D9_sl_79_211_orb3f0_s1.txt, 1.1·10⁴ evaluations).

Any valid group above 104,014,560 is a new record. The target is therefore any N ≥ 104,014,561, not a jump.

## Previous rounds (do not repeat)

- Round 1 (branch claude/raise-d15d9-record-sx33j8): five runs cut off near 400 s, cost > 0 throughout. Best open
  lead then: prod SL(2,5) × SL(2,19) × Z127 at cost 14.
- Round 2 (branch claude/raise-d15d9-record-r2-0c41x5, full notes in research/squads/cells/raise-d15D9.md there):
  ten runs of 2–3 h on the lowest-μ admissible groups, plain and ORBW=5, seeds 1–7. Best costs:
  - prod SL(2,5) × SL(2,19) × Z127 (N = 104,241,600, μ 24.92): 8, 8, 10 (plain / RESTART), 6, 6 (ORBW=5, seeds 4, 5),
    12, 12 (ORBW=5, seeds 6, 7). Cost 6 is the floor. Plateaus at 6–8 for long stretches.
  - prod SL(2,5) × SL(2,13) × Z397 (N = 104,045,760, μ 24.17): 20 (one run, plain only; ORBW=5 not tried).
  - SL(2,53) × Z703: 24. SL(2,41) × Z1519: 42.
  - Nothing reached cost 0.

## Round 3 notes

### Admissible candidates in the window (orb_screen.py, two-factor products, plus triple_screen.py)

The filters are those of round 2: no PSL/PGL factor (involutions, bad at odd D), no characteristic 2, no SL(2,3),
Z_n with every prime ≡ 1 mod 3. Ordered by N:

| N | group | μ | notes |
|---|---|---|---|
| 104,045,760 | prod SL(2,5) × SL(2,13) × Z397 | 24.17 | lowest μ; round 2 plain cost 20 |
| 104,126,400 | prod SL(2,5)² × Z7231 | 24.3 | large cyclic factor: expected to mix badly |
| 104,241,600 | prod SL(2,5) × SL(2,19) × Z127 | 24.92 | round 2 best (cost 6) |
| 104,307,840 | prod SL(2,5) × SL(2,7) × Z2587 | 24.9 | large cyclic factor |
| 104,546,400 | SL(2,49) × Z889 | 26.1 | needs a GF(49) checker |
| 104,569,920 | prod SL(2,13) × SL(2,19) × Z7 | 26.2 | not in round 2 |
| 104,623,272 | SL(2,53) × Z703 | 26.4 | round 2 cost 24 |
| 104,628,720 | SL(2,41) × Z1519 | 26.5 | round 2 cost 42 |
| 104,702,400 | prod SL(2,5) × SL(2,11) × Z661 | 26.8 | not in round 2 |

The next admissible orders are above 104.8M. Groups with a PSL factor (e.g. prod PSL(2,7) × SL(2,7) × Z1843 at
104,033,664) are excluded by the involution argument (STRUCTURE §2.6).

### Wave 1 (started 01:40 UTC, 8,100 s each, ORBIT="3 5 0", ORBW=5, RESTART=1, K = 8, THREADS=1)

| job | group | N | settings | seed |
|---|---|---|---|---|
| s41 | prod SL(2,5) × SL(2,19) × Z127 | 104,241,600 | ORBW=5, RESTART=1 | 41 |
| s42 | prod SL(2,5) × SL(2,19) × Z127 | 104,241,600 | ORBW=5, RESTART=1 | 42 |
| s43 | prod SL(2,5) × SL(2,13) × Z397 | 104,045,760 | ORBW=5, RESTART=1 | 43 |
| s44 | prod SL(2,5) × SL(2,13) × Z397 | 104,045,760 | ORBW=5, RESTART=1, TMIN 0.4, TMAX 2.0 | 44 |

Logs: /home/user/scratch_r3/logs/ until the jobs end; copies go to research/structured/runs/raise3_*.log at each checkpoint.


## Checkpoint, 02:17 UTC (round 3, wave 1, about 2,300 s in, ~5,500 evals each)

| job | group | settings | evals | best cost |
|---|---|---|---|---|
| s41 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 5,561 | 18 |
| s42 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 5,545 | 6 |
| s43 | prod SL(2,5) × SL(2,13) × Z397 | ORBW=5, RESTART=1 | 5,585 | 30 |
| s44 | prod SL(2,5) × SL(2,13) × Z397 | ORBW=5, RESTART=1, TMIN 0.4, TMAX 2.0 | 5,593 | 42 |

Logs copied to research/structured/runs/raise3_*.log. Nothing at cost 0 yet. The 5×13×397 group is far behind 5×19×127 so far.

## Wave 1 final (ended 03:52 UTC, 8,100 s each, 19,200–19,400 evals)

| job | group | settings | evals | best cost |
|---|---|---|---|---|
| s41 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 19,321 | 6 |
| s42 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 19,241 | 6 |
| s43 | prod SL(2,5) × SL(2,13) × Z397 | ORBW=5, RESTART=1 | 19,377 | 30 |
| s44 | prod SL(2,5) × SL(2,13) × Z397 | ORBW=5, RESTART=1, TMIN 0.4, TMAX 2.0 | 19,377 | 30 |

No solution. Logs: research/structured/runs/raise3_*.log.

Reading:
- 5×19×127 with ORBW=5 has now reached cost 6 in four of its runs (round 2 seeds 4 and 5, round 3 seeds 41 and 42).
  That is a floor, not a trend: it is reached in the first 1–2 h and then does not move. Cost 6 means two uncovered
  free orbits, or fixed points that are covered in pairs.
- 5×13×397 is worse at this budget: cost 30 in both runs. A wider TMIN did not help (it was at 36–42 earlier, then
  the same 30 floor). Its Z397 factor is the largest cyclic factor of the admissible set, so mixing is the likely
  reason.
- α is fixed per group (choose_alpha picks one conjugacy-class representative by a deterministic rule). Different
  seeds therefore share α. Within one group, a different α is conjugate to this one by an inner automorphism, so it
  gives an isomorphic search space, not a new one. The seed changes only the starting S.

## Wave 2 (started 03:52 UTC, 7,200 s each)

| job | group | settings | seed |
|---|---|---|---|
| s51 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 51 |
| s52 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 52 |
| s53 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 53 |
| s54 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1, K=4 | 54 |

Status: running. Nothing at cost 0 yet.

## Wave 2 final (3,424 s to the find; other seeds stopped at ~3,500 s)

| job | group | settings | evals | best cost |
|---|---|---|---|---|
| s51 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | ~8,400 | 18 |
| **s52** | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 8,385 | **0 (solution)** |
| s53 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | ~8,400 | 12 |
| s54 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1, K=4 | ~8,100 | 12 |

Seeds 51, 53, 54 were stopped after the find: they are on the same N and cannot raise the record. The find came from a
run whose plateau had sat at 12 for about 1,000 s, which says a plateau is not a stop signal, but one hit in four
seeds at this group is also the only success so far on 5×19×127 (round 2 seeds 4–7 and round 3 seeds 41, 42, 51–54
gave 6–36).

## Next: records above 104,241,600

A new record must have |G| > 104,241,600. Admissible candidates just above (same filters as before):

| N | group | μ | Fix | notes |
|---|---|---|---|---|
| 104,299,200 | prod SL(2,5) × SL(2,5) × Z7243 | ~25.1 | | large cyclic factor |
| 104,307,840 | prod SL(2,5) × SL(2,7) × Z2587 | ~25.2 | 36 | large cyclic factor |
| 104,569,920 | prod SL(2,13) × SL(2,19) × Z7 | ~26.2 | | small Z |
| 104,702,400 | prod SL(2,5) × SL(2,11) × Z661 | ~26.8 | | round 2 "next" |

Status and any wave 3 results: see the sections below.

## Wave 3 (started 04:57 UTC, groups above 104,241,600; checkpoint 05:28 UTC)

| job | group | N | μ | Fix | settings | cost at 05:28 |
|---|---|---|---|---|---|---|
| s61 | prod SL(2,5) × SL(2,7) × Z2587 | 104,307,840 | 25.18 | 35 | ORBW=5, RESTART=1 | 336 (stopped, large cyclic factor) |
| s62 | prod SL(2,5) × SL(2,5) × Z7243 | 104,299,200 | 25.15 | 35 | ORBW=5, RESTART=1 | 1,770 (stopped after 600 s, large cyclic factor) |
| s63 | prod SL(2,13) × SL(2,19) × Z7 | 104,569,920 | 26.23 | 215 | ORBW=5, RESTART=1 | 12 |
| s64 | prod SL(2,5) × SL(2,11) × Z661 | 104,702,400 | 26.77 | 71 | ORBW=5, RESTART=1 | 74 (stopped) |
| s65 | SL(2,53) × Z703 | 104,623,272 | 26.45 | 53 | ORBW=5, RESTART=1 | 30 |
| s66, s67 | prod SL(2,13) × SL(2,19) × Z7 | 104,569,920 | 26.23 | 215 | ORBW=5, RESTART=1, started 05:27 UTC | running |

The large cyclic factors (Z2587, Z7243) cover far worse than any group tried here: the start cost is already 1,600–25,000
and annealing does not bring it under about 300. They were dropped. Cores moved to SL(2,13) × SL(2,19) × Z7 (cost 12 at
about 4,300 evals, the best of this wave so far).

## Wave 3 final (06:50–07:17 UTC)

| job | group | N | evals | best cost |
|---|---|---|---|---|
| s61 | prod SL(2,5) × SL(2,7) × Z2587 | 104,307,840 | 4,873 | 316 (stopped at 1,857 s) |
| s62 | prod SL(2,5) × SL(2,5) × Z7243 | 104,299,200 | 425 | 1,770 (stopped at 627 s) |
| s63 | prod SL(2,13) × SL(2,19) × Z7 | 104,569,920 | 16,209 | 6 (7,000 s) |
| s64 | prod SL(2,5) × SL(2,11) × Z661 | 104,702,400 | 3,457 | 74 (stopped at 1,856 s) |
| s65 | SL(2,53) × Z703 | 104,623,272 | 25,529 | 18 (7,000 s) |
| s66 | prod SL(2,13) × SL(2,19) × Z7 | 104,569,920 | 15,393 | 6 (6,600 s) |
| s67 | prod SL(2,13) × SL(2,19) × Z7 | 104,569,920 | 15,577 | 2 (6,600 s, closest run of the round) |

No solution above 104,241,600 in wave 3. Seed 67 ended at cost 2 (one fixed point or one orbit short). The best group here, SL(2,13) × SL(2,19) × Z7 (μ 26.2), sits at the same
cost-6 floor as 5×19×127. Its μ is about 5% above the record group, so the same effort buys a lower chance.

## Status at the end of the session

- Record: 208,483,200 vertices (|G| = 104,241,600), on the branch and in research/frontier/sols/ (verified).
- Next step-up needs |G| > 104,241,600. The lowest admissible candidates there are 13×19×7 (104,569,920) and
  SL(2,53)×Z703 (104,623,272). Both reached cost 6 and 18 at about 2–4 h, with no cost 0. The large-cyclic-factor
  candidates (Z2587, Z7243) are far off and not worth more core-hours with this search.
- Honest read: five 2-h runs on a μ ≈ 25–26 group gave one solution in about 25 runs of this method across rounds 2
  and 3 (the lucky seed 52 at 8,385 evals). More seeds on 13×19×7 and on the two next groups are the only
  straightforward continuation. No structural change was found here.
