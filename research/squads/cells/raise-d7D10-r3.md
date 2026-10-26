# Cell (Δ, D) = (7, 10): raise job, round 3

Haiku worker session on `claude/raise-d7d10-record-r3-jjzcps` (2026-10-26). Round 1 is `research/squads/cells/raise-d7D10.md`
and round 2 is `research/squads/cells/raise-d7D10-r2.md` (branch `claude/raise-d7d10-record-r2-5y95db`). Both are imported
here; read them first. Their solution files and run logs are copied in as they were.

## Record to beat

**2,298,240 vertices** (N = 1,149,120), SL(2,7) × PSL(2,19), no Z factor, k = 3, m = 2, f = 1, seed 2.
File: `research/frontier/sols/d7D10_prod_sl_7_psl_19_1_orb3_s2.txt`.
Re-verified in round 3 with `build_haar2.py`: VALID, d = 7, D = 10, n = 2,298,240, 7-regular, no duplicate edges, both ecc 10,
edge-list sha256 `d977a1225993a74ae9c26e3c021d40a3e287407595eea0e499c11e74c14cd0fe` (same as round 2).

The brief's 2,237,760 is superseded (round 2 already raised the record twice). Target this round: any verified (7,10) Haar
graph with N > 1,149,120.

## Where the k = 3 orbit method stands

- Round 2 ran the window N = 1,155,960–1,172,000 and nothing solved. Its best costs: sl 19 × Z169 5 (seed 11, 60 min, still moving
  at the end), pgl 19 × Z169 9 (RESTART=1), psl 19 × Z337 18 (11 min only), sl 16 × Z283 27 (11 min only).
- The record is at μ ≈ 31. Each +0.1 % in N raises μ by ≈ 1.2 %, so the window above the record has μ ≈ 32–34. The window is
  narrow: the candidate screen `orb_screen.py 7 10 1149121 1160000 "3 2 1" --list` gives exactly 8 groups (all with n's prime
  factors ≡ 1 mod 3).

## Round 3 plan (this session)

1. Four 2-hour single-thread anneals with `ORBIT="3 2 1"` on the top window candidates (round 2's untried compute: longer
   runs on the one group that was still moving):
   - sl 19 × Z169, seed 41 (plain)
   - sl 19 × Z169, seed 42 (plain)
   - pgl 19 × Z169, seed 43, RESTART=1
   - sl 19 × Z169, seed 45, ORBW=3 (fixed elements weigh 3)
2. Order-2 orbits (k = 2, f = 1, m = 3). Round 1 and round 2 never tried k = 2 at (7,10). SIZE_LAW-style counting gives
   about e^8 more solution orbit-sets than k = 3 at the same μ, but each orbit miss costs more. Screened first with
   `orb_screen.py 7 10 1100000 1160000 "2 3 1" --samples 200` against the k = 3 screen (results below).

## Progress log

- 2026-10-26: imported round-2 solutions, runs and notes; built `research/structured/haar_sym` and
  `tools/haarcheck_psl` from the committed sources; re-verified the record (VALID). Launched the four runs above
  (scratchpad `runs/`, logs copied to `research/structured/runs/` when they finish).
- 2026-10-26, order-2 screen (`orb_screen.py 7 10 1100000 1160000 "2 3 1" --samples 200 --nmax 1000`, 5 min): NEGATIVE.
  Sampled p1 of random symmetric S at N ≈ 1.10–1.16 M: the record group prod sl 7 psl 19 (μ 30.9, |Fix| 159) has p1 31, against
  p1 ≈ 24 for the same group under k = 3 (round 2). Groups at μ 32–34 have p1 in the hundreds or thousands (e.g. psl 23 × Z191 942,
  pgl 27 × Z59 298). Involutions bring many fixed points and word collisions, so k = 2 is dropped for this cell.
- Checkpoint 2026-10-26 (t ≈ 330 s of 6900 s): sl 19 × Z169 seeds 41 and 42 at cost 9, pgl 19 × Z169 RESTART at 12,
  sl 19 × Z169 ORBW=3 at 9.
