# squad-alone-2: Haar graphs with an order-3 or order-5 orbit symmetry, target (16,5) > 31,460 vertices

Worker job "squad-alone-2" (Haiku, no Opus direction). Region: Haar graphs H(G,S), |S| = 16, S closed under an
automorphism α of order 3 or 5 (`haar_sym`, ORBIT mode). Question: can such a graph beat 31,460 vertices?

## Verdict

**No.** Nothing in this region reached 31,460, or the table value 27,300. Best VALID graph: **22,320 vertices**
(k = 5, f = 1, m = 3, S on PSL(2,9) × Z31, N = 11,160). It is below the table, so it is not a record for us.

## Why this region cannot reach the target (counting)

- D = 5 is odd: each of the two covering conditions uses W = 1 + Σ_{i≤2} Δ(Δ−1)^(2i−1) = 1 + 240 + 54,000 = 54,241
  words. The target needs N ≥ 15,731 (|V| = 2N ≥ 31,462).
- Random-like S at N = 15,731 gives Poisson mean μ = N e^(−W/N) ≈ 500 uncovered (total over both conditions).
  The first-moment ceiling μ ≈ Δ ln N ≈ 155 is crossed near N_h ≈ 12,300 (|V| ≈ 24,600). The target is about 1.28·N_h.
- Orbit symmetry divides the μ that matters by k (μ_eff ≈ μ/k + fixed-point misses). It does not move the ceiling
  (SIZE_LAW §1.4; STRUCTURE.md §1). At the target order, μ_eff ≈ 167 (k = 3) and ≈ 100 (k = 5). Both are far above the
  orbit wall (μ ≈ 50–90 in our runs).

## Measurements (haar_sym, THREADS = 4, one seed unless stated)

Solved (VALID, checked by `build_haar2.py`):

| k, f, m | group | N | |V| = 2N | result |
|---|---|---|---|
| 5, 1, 3 | PSL(2,9) × Z31 | 11,160 | **22,320** | solved, 1.05 M evals; **best valid** |
| 5, 1, 3 | PSL(2,5) × Z181 | 10,860 | 21,720 | solved, 3.1·10⁴ evals |
| 5, 1, 3 | PSL(2,5) × Z151 | 9,060 | 18,120 | solved, 73 evals |
| 3, 1, 5 | PSL(2,7) × Z61 | 10,248 | 20,496 | solved, 0.8 s |
| 3, 1, 5 | PGL(2,4) × Z151 | 9,060 | 18,120 | solved, 0.0 s |

Not solved, best cost in brackets (cost = uncovered, total over both conditions):

| k | group | N | |V| | μ | best cost, runtime |
|---|---|---|---|---|---|
| 3 | PGL(2,7) × Z31 | 10,416 | 20,832 | 57 | 3 (60 s); **1 (300 s, 6.2·10⁷ evals)**; 6 with ORBW=3 (300 s) |
| 3 | PGL(2,4) × Z181 | 10,860 | 21,720 | 74 | 18 (60 s) |
| 3 | PSL(2,9) × Z31 | 11,160 | 22,320 | 87 | 14 (60 s) |
| 3 | PSL(2,7) × Z67 | 11,256 | 22,512 | 91 | 23 (60 s) |
| 3 | PGL(2,5) × Z97 / PGL(2,4) × Z193 | 11,640 / 11,580 | 23,160–23,280 | 107–110 | 29 / 53 (60 s) |
| 5 | PGL(2,4) × Z191 | 11,460 | 22,920 | 101 | 14 (60 s), 12 (120 s ORBW=5), **12 (300 s, 4.5·10⁷ evals)** |
| 5 | PGL(2,5) × Z101 | 12,120 | 24,240 | 138 | 29 (60 s); 22 (120 s ORBW=5) |
| 5 | PGL(2,4) × Z211 | 12,660 | 25,320 | 175 | 72 (60 s) |
| 5 | PSL(2,29) | 12,180 | 24,360 | 142 | 111 (60 s) |
| 5 | PSL(2,5) × Z241 | 14,460 | 28,920 | 340 | 259 (60 s) |
| 3 | PGL(2,4) × Z217 | 13,020 | 26,040 | 202 | 156 (120 s) |
| 3 | SL(2,9) × Z19 | 13,680 | 27,360 | 259 | 166 (120 s) |
| 3 | SL(2,7) × Z43 | 14,448 | 28,896 | 338 | 266 (120 s) |
| 3 | PGL(2,5) × Z133 | 15,960 | 31,920 | 533 | 579 (120 s, 9.7·10⁶ evals) |

Random symmetric S at N = 15,731–16,600 (60 samples per group, k = 3): the best sampled cost is 760–1,020, and the
median is about 1,450. Annealing cuts the cost by about 60 % in two minutes and then plateaus.

## What the curve says

- **Sharp wall, not a slow slope.** Every rung up to N ≈ 11,160 is solved or within a few units of 0. Above that the
  best cost rises roughly linearly with μ (cost ≈ 0.3–0.6 μ), and it is not improved by 5× more time or by fixed-point
  weighting (ORBW). Cost 0 is not reached at any N ≥ 11,460 in 60–300 s runs.
- **k = 5 is better than k = 3 here.** It solves at 22,320 and stays at cost 12–14 up to 22,920. The k = 3 wall is
  about 20,500–20,800. Both sit at about 0.9·2N_h.
- **Fixed-point weighting did not help.** ORBW = k helped one k = 5 rung (14 → 12, 29 → 22) and hurt the k = 3 rung
  (1 → 6). The fixed points are not the whole story.
- **The 300 s k = 3 run on PGL(2,7) × Z31 ends at cost 1.** That is the closest miss, at |V| = 20,832, and still below
  our best valid 22,320.

## Checks

- Every VALID entry above passed `research/frontier/build_haar2.py` (all BFS from both sides, exact diameter 5, degree
  16, no duplicate edges). Output in `sols/*.log` and `check_output.txt` next to this file.
- Solution files (haar_gen3 format, first generator e) are in `sols/`.
- Not re-checked and not counted: a run on PGL(2,3) × Z379 (N = 9,096) reported cost 0 within 1.6 s, but I
  did not run build_haar2 on it.

## Scope and honesty

- Within this region, 31,460 is not reached and cannot be reached by counting. The data agree with the counting.
- 22,320 is our best valid order in this region, not a new record. The table value for (16,5) is 27,300, and we did
  not reach it.
- Other ideas not tried (outside the brief or out of time): fixed generators beyond f = 1 for k = 5, groups with a
  smaller centralizer (SL(3,q), noted in STRUCTURE.md §7), and voltage lifts over Moore/GQ structures. The
  counting argument does not rule these out, but none is a Haar-orbit search.

## Files

- `scoreboard.jsonl`: one JSON line per serious attempt (score = |V| if valid, else best cost).
- `sols/`: four VALID solutions plus the k = 5 psl 9 × 31 solution, with logs.
- `check_output.txt`: build_haar2.py output for the VALID entries.
