# Raise the (Δ,D) = (6,9) record: notes for resumption

Job "raise-6-9" (Haiku worker). Record to beat: **127,296 vertices** (Haar graph of SL(2,17) × Z13, N = 63,648,
orbit k=3, m=2, f=0; `research/frontier/sols/d6D9_sl_17_13_orb3f0_s2.txt`). Table 117,360; Moore 976,562.
Every new record needs N ≥ 63,649 (vertices = 2N).

## Method

- Tool: `research/structured/haar_sym` (orbit-symmetric annealing, STRUCTURE.md §1, §8). Build:
  `gcc -O3 -march=native -fopenmp haar_sym.c -o haar_sym -lm` (warnings only).
- Command shape: `ORBIT="3 2 0" haar_sym 6 9 <secs> <seed> 8 <out> <group> <n>`, THREADS=1, under nice.
- Reproduced the record: `sl 17 13`, seed 2, 34k evaluations, 2.7 s.
- Candidate orders from `tools/orb_screen.py 6 9 63649 80000 "3 2 0" --list` (μ = N e^(−W/N), W = 488,281).
  Each +1 % in N raises μ by about 9 %. Evaluations to solve grow like e^(μ/4.5) (STRUCTURE §3, §8).
- Job queue: `tools/pool.sh` with spool `<scratchpad>/spool`, `tools/orbq.sh` per job file. Solutions and
  logs go to the spool; a VALID one is copied into `research/frontier/sols/` and `research/structured/runs/`.

## Log

- (start) binary builds, record reproduces. Wave 1: μ ≈ 30–40 candidates, 600 s, seed 1.
- Wave 1 batch A (600 s, seed 1, ~9e6 evals each, all unsolved):
  sl 8 × 127 (N 64008, μ 31.1): best 46; psl 7 × 379 (N 63672, μ 29.7): best 138;
  sl 11 × 49 (N 64680, μ 34.1): best 14; sl 7 × 193 (N 64848, μ 34.8): best 96.
  Reading: group family matters more than μ. Small q (7, 8) and psl 7 are poor. The record's group
  SL(2,17) × Z13 solved at μ 29.7 in ~6e4 evals. Prefer large prime q with small prime n.
- Candidates still open, N ≥ 63,649 with every prime of n ≡ 1 mod 3 (orb_screen list): psl 19×19 (64980),
  psl 11×97 (64020), psl 13×61 (66612), sl 13×31 (67704, μ 50), psl 9×181 (65160), sl 41×1 (68880, μ 57.5),
  psl 27×7 (68796), sl 9×91 (65520).
- Wave 1 batch B (600 s, seed 1): psl 19 × 19 (N 64980, μ 35.4, |Fix| 8): **best 3** (6.4M evals);
  psl 13 × 61 (N 66612, μ 43.7): best 12; psl 11 × 97: best 18; sl 9 × 91: best 62;
  psl 9 × 181 (N 65160): best 84; sl 41 × 1 (N 68880, μ 57.5, |Fix| 41): best 24.
- Wave 2: psl 19 × 19 seeds 2, 3 at 1200 s: both stuck at 3 after 5.3M evals. ORBW=3 variant (seeds 1, 2).
  Odd D and PSL: PSL(2,q) has ~q²/4 involutions, each missed with prob about e^(−λ/2), so a floor of a few
  misses is expected (STRUCTURE §2.6, §5). SL(2,q) has only −I. That may explain the plateau at 3.
- Wave 3 (queued): sl 13 × 31 (N 67704, μ 49.9, large q so small |Fix|), seeds 1, 2 at 1200 s.
