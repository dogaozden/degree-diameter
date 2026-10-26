# Cell (Δ, D) = (9, 8): raise-9-8 job, round 3 (Haiku worker)

Branch `claude/raise-d9d8-haar-round3-sf2qfg`. Record: **546,720** vertices (sl 16 × Z67, k = 3, m = 3, f = 0, solutions
`research/frontier/sols/d9D8_sl_16_67_orb3f0_r2s{21,23,24}.txt`, from round 2). Table value 449,480; Moore bound 4,793,490.

## What rounds 1 and 2 did (do not repeat)

- Round 1 (`claude/raise-d9d8-haar-record-rqmcq3`): k = 3, f = 0, 12 groups at N = 270,312 to 277,860, none solved.
- Round 2 (`claude/raise-d9d8-haar-round2-q5t083`): sl 16 × Z67 solved (3 seeds). Next rungs stalled: prod sl 5 × sl 5 × Z19
  (μ 42.9, best cost 1), sl 13 × Z127 (μ 49, round 1 best 6), groups with μ > 49 not run.
- Ruled out in rounds 1–2: k = 3 with more seeds on the same group; k = 5 and 7 at this order (no small-fixed-set
  automorphisms); a single order-9 orbit; Frobenius; Heisenberg, AGL(1,p) and metacyclic scalings.

## Round 3: a new configuration, k = 4, f = 1, m = 2

With k = 4, d = 9 = f + k·m forces f = 1 (S = {e} ∪ O₁ ∪ O₂, two α-orbits of size 4). Neither earlier round tried k = 4.
The wall argument of STRUCTURE.md §3 (k-orbit cost ≈ μ/k) predicts k = 4 reaches μ ≈ 4/3 × 48 ≈ 64 before stalling,
i.e. N ≈ 285,000, against N = 273,360 for k = 3. Random-sample count to hit zero is about e^(μ/4) (k = 3: about e^(μ/3)).

Candidates (`research/structured/tools/orb_screen.py 9 8 273361 292000 "4 2 1" --samples 200`, log
`runs/raise_d9D8_r3/screen_k4_f1_m2.txt`): best by (p1+p10)/2 of random-S cost:

| group | N | μ | |Fix| | min | p1 | p10 | median |
|---|---|---|---|---|---|---|---|
| prod psl 7 × sl 7 × Z5 | 282,240 | 57.9 | 31 | 36 | 58 | 85 | 244 |
| psl 17 × Z113 | 276,624 | 47.8 | 7 | 104 | 178 | 281 | 1,836 |
| pgl 19 × Z41 | 280,440 | 54.5 | 19 | 119 | 126 | 198 | 2,341 |
| psl 25 × Z37 | 288,600 | 71.4 | 11 | 98 | 124 | 181 | 569 |

Runs (haar_sym, THREADS = 1, 900 s each, logs and solutions in `runs/raise_d9D8_r3/`, launcher `launch_k4.sh`):
seeds 41 (prod psl 7 × sl 7 × Z5), 42 (pgl 19 × Z41), 43 (psl 17 × Z113), 44 (psl 25 × Z37).

(Results appended below as they come in.)

### Results, first 900 s (seeds 41–44, default settings, about 2–4·10⁶ evaluations each)

| seed | group | N | μ | |Fix| | start → best cost |
|---|---|---|---|---|---|
| 41 | prod psl 7 × sl 7 × Z5 | 282,240 | 57.9 | 31 | 169 → **11** (flat from 800 s) |
| 42 | pgl 19 × Z41 | 280,440 | 54.5 | 19 | → 48 |
| 43 | psl 17 × Z113 | 276,624 | 47.8 | 7 | → 48 |
| 44 | psl 25 × Z37 | 288,600 | 71.4 | 11 | → 42 |

Reading: cost is the orbit energy (uncovered/k, plus fixed-point misses). No k = 4 run solved in 900 s; the best
(seed 41) stalled at T = 0.15 with cost 11. The naive wall estimate (μ/k ≈ 16–18, so μ ≈ 64 for k = 4) is not borne out
at 2–4·10⁶ evaluations: the k = 4 groups at μ 48–58 are not yet at the level where k = 3 (sl 16 × Z67) solved.

### Anyn screen (`runs/raise_d9D8_r3/screen_k4_f1_m2_anyn.txt`, n with primes ≡ 3 mod 4 allowed, so α = conj·(z ↦ −z) style)

Best by min cost: prod psl 7 × sl 7 × Z5 (min 36, same as before), then psl 41 × Z8 (N 275,520, μ 45.9, |Fix| 39, min 58),
psl 17 × Z117 (N 286,416, μ 66.5, |Fix| 7, min 60), psl 17 × Z119 (N 291,312, μ 77.8, min 86).

### Second round, seeds 51–54, 5,400 s each (launched 2026-10-26, `launch_k4.sh`)

- 51: prod psl 7 × sl 7 × Z5, ORBW=4 (fixed-point misses ≈ 3.8)
- 52: prod psl 7 × sl 7 × Z5, ORBW=4, RESTART=1
- 53: psl 17 × Z117 (N 286,416, μ 66.5), ORBW=4
- 54: psl 17 × Z117, default

(Results appended below as they come in.)
