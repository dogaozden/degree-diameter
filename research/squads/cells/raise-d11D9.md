# Cell (Δ,D) = (11,9): raise the record above 16,792,080

Job "raise-11-9" (Haiku worker, branch claude/raise-d11d9-record-2x1d57). Goal: a Haar graph H(G,S) with
|G| > 8,396,040 (2|G| > 16,792,080), 11-regular, diameter 9, verified.

## Current record and why it is where it is

- Record: sl 61 × Z_37 (|G| = 8,396,040), orbit k = 3, m = 3, f = 2, μ = 15.0, solved after 4,969 evaluations
  (`research/structured/runs/d11D9_sl_61_37_orb3_s1.log`, `research/frontier/sols/d11D9_sl_61_37_orb3_s1.txt`).
- μ = N e^(−W/N), W = 111,111,111 for (11,9). μ ladder (largest |G| with μ ≤ m):
  μ 15 → 8.395M, μ 20 → 8.568M, μ 25 → 8.707M, μ 30 → 8.824M, μ 35 → 8.925M, μ 40 → 9.015M.
  So each unit of μ buys about 0.1–0.2 % in |G| near here; the gains come from running at higher μ.
- Evaluation cost: sl 61 × Z37 (wide rows) ≈ 0.05 s/eval; sl 31 × Z283 (no cyclic subgroup of order ≥ 64, haar_gen3
  evaluation) ≈ 0.023 s/eval, single thread.
- Earlier attempts at this cell in research/structured/runs: psl 257 × Z1 stalled at cost 73 (involutions, odd D);
  sl 107 × Z7 stalled at cost 2 after 40k evals; psl 61 × Z73 solved but is smaller (8,282,580).

## Rules of thumb used

- SL-type groups only (no PSL factor): odd D has involution misses with PSL (see research/structured/STRUCTURE.md §2.6).
  Char-2/3 groups kept out except SL(2,4), SL(2,8) factors (few involutions).
- n has all prime factors ≡ 1 (mod 3).
- ORBIT="3 3 2" (d = 2 + 3·3 = 11), K = 8, THREADS = 1, nice.

## Driver

`scratchpad` (not in repo): `job.sh SECS SEED GROUP...` runs `haar_sym 11 9 SECS SEED 8 out GROUP`, then checks any
solution with two independent low-memory checkers (`research/frontier/haarcheck_sl.c`, `haarcheck2.c`); prod
groups need `build_haar2.py` instead.

## Log

- 2026-10-25 wave 1 (1200 s, seed 1, 4 at a time): 18 SL-only candidates from μ 15.3 to 30.2. Results in the table below.

## Result 1: NEW RECORD (11,9), 16,853,760 vertices (was 16,792,080, +0.36 %)

- Group prod sl 7 × sl 11 × Z_19, |G| = 8,426,880, orbit k = 3, m = 3, f = 2, μ = 15.8. Solved at evaluation 11,545 (wave 1, seed 1, 281 s).
- Solution: research/frontier/sols/d11D9_prod_sl_7_sl_11_19_orb3_s1.txt. Search log: research/structured/runs/d11D9_prod_sl_7_sl_11_19_orb3_s1.log.
- Independent check: build_haar2.py (rebuild from definitions): ecc 9 from (e,A) and (e,B), 0 unreached, VALID d=11 D=9,
  edge list sha256 280a20185193497c49a74d56b8e89929c74a8ca632540b58c6b7c398d9305de3. Log: runs/d11D9_prod_sl_7_sl_11_19_orb3_s1.rebuild.txt.
- The SL checkers (haarcheck_sl / haarcheck2) do not read prod headers; build_haar2 is the checker for prod groups.
