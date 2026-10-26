# Cell (Δ, D) = (15, 9): raise job raise-15-9, round 3 (branch claude/raise-d15d9-record-r3-u6folv)

Goal: beat our record 208,029,120 vertices, i.e. a Haar graph with |G| ≥ 104,014,561 (2|G| vertices, 15-regular,
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

## Status

Wave 1 running. Nothing reached cost 0 at the time of writing; see the LOG entry for results.

## Checkpoint, 02:17 UTC (round 3, wave 1, about 2,300 s in, ~5,500 evals each)

| job | group | settings | evals | best cost |
|---|---|---|---|---|
| s41 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 5,561 | 18 |
| s42 | prod SL(2,5) × SL(2,19) × Z127 | ORBW=5, RESTART=1 | 5,545 | 6 |
| s43 | prod SL(2,5) × SL(2,13) × Z397 | ORBW=5, RESTART=1 | 5,585 | 30 |
| s44 | prod SL(2,5) × SL(2,13) × Z397 | ORBW=5, RESTART=1, TMIN 0.4, TMAX 2.0 | 5,593 | 42 |

Logs copied to research/structured/runs/raise3_*.log. Nothing at cost 0 yet. The 5×13×397 group is far behind 5×19×127 so far.
