# squad-alone-4: prod-family Haar search, Δ = 16, D = 5

Worker squad-alone-4 (Haiku, no Opus direction). Region: Haar graphs H(G,S) over direct products of two small groups
(the `prod` family of haar_gen3). Target: bipartite, Δ = 16, D = 5, more than 31,460 vertices, i.e. |G| ≥ 15,731
(the graph has 2|G| vertices).

## Result

**Target not reached.** Best valid graph in this region: G = PSL(2,7) × Z₅₆ (|G| = 9,408, **18,816 vertices**), and
also SL(2,7) × Z₂₈ (|G| = 9,408). Both pass build_haar2.py (VALID, max degree 16, diameter 5 from both sides, no
duplicate edges). This is about 60 % of the target and below the 2013 table entry 27,300 for (16,5).

Every candidate of order 15,731 or more failed: 15 groups at 15,840–18,000, best cost 496–1,075 uncovered elements after
240 s (one 600 s run on A5×A5×Z3 at 10,800 was 42). Nothing at 9,744 or above solved, even at 1,200 s (PSL(2,7)×Z₅₈ 5 left, SL(2,7)×Z₂₉ 2 left). Just below the
best, PSL(2,11)×Z₁₄ (9,240) ends at 1 uncovered and PSL(2,9)×Z₂₆ (9,360) at 2 after 1,200 s.

## Why this family stalls (size law, same as the other squads)

- Word bound for Δ = 16, D = 5: W = 1 + Δ(Δ−1) + Δ(Δ−1)³ = 54,241. Random-model first moment:
  N_h from N e^(−W/N) = Δ ln N is 12,318.
- Random model μ = N e^(−W/N): μ = 8 at N = 7,920; 23 at 9,072; **30 at 9,408** (our wall); 37 at 9,744; 516 at 15,840.
  The size-law wall is μ* ≈ 25 at N ≈ 9,400 (ln μ* = 4.34 − 0.123 ln N, research/frontier/SIZE_LAW.md). The observed
  wall matches it.
- At 15,840 the annealing ends with 496–541 uncovered elements, i.e. the same order as μ ≈ 516. Annealing over these
  groups behaves like random Haar sets; the group choice changes the picture by at most a factor of about 2.
  The target needs μ ≈ 500 to be solvable, about 20× the wall.

## Calibration and comparisons

- Abelian control: Z₈₄₀₀ (meta 8400 1 1, N = 8,400), 200 s: best 1,266 uncovered. PSL(2,7) × Z₅₀ of the same order
  solves in under 1 s. The non-abelian factor is what matters.
- Two non-abelian factors: A₅×A₅ (= psl 5 × psl 5) × Z_n: n = 2 (N = 7,200) solves; n = 3 (10,800) ends at 34–42
  uncovered; n = 4 (14,400) at 436; n = 5 (18,000) at 1,075. A₅×A₅ does not beat the single-factor groups.
  SL(2,5) × PSL(2,5) (sl 5 × psl 5, N = 7,200) solves.
- AGL(1,11) × AGL(1,13) (N = 17,160): 789 uncovered.
- PSL(2,8) × Z_n: solves up to n = 17 (N = 8,568); n = 18 (9,072) at 2 uncovered after 200 s.
- PSL(2,9) = A₆ × Z_n: solves up to n = 24 (8,640); n = 26 (9,360) at 2 after 1,200 s.
- PGL(2,7) × Z_n: solves at N = 8,400; N = 9,408 at 4 after 300 s.
- PSL(2,13) × Z₁₅ (16,380): 617; PSL(2,13) × Z₁₆ (17,472): 924.

## Verification

- All 20 valid solutions in `sols/` were rebuilt and checked independently with
  `research/frontier/build_haar2.py` (20 VALID lines, see `sols/*.check`). Exact diameter for Haar graphs follows from
  two BFS (from (e,A) and (e,B)) because right multiplication is transitive on each side.
- Best graph: `sols/psl7_meta56_long.txt` (haar_gen3 format), edge list `sols/psl7_meta56_long.edges.txt.gz`,
  check output `sols/psl7_meta56_long.check` (sha256 of edge list `40bd75c3…62f5c9`).
- Second 9,408 solution: `sols/sl7_meta28_long.txt`, check `sols/sl7_meta28_long.check`.
- No record claimed. The table entry (16,5) is 27,300, far above what this family reaches.

## Not tried (and why)

- Symmetric S (orbits of an automorphism) and 2+2 lifts: the size-law note says symmetric S is worse, and 2+2 lifts are
  not a Haar graph, so they are outside this region.
- Product-set S = S1×S2 (|S1|·|S2| = 16) and S chosen by algebra: not tested. A product set makes (S⁻¹S)² a product
  A1×A2, a strong restriction, which I did not explore.
- Longer runs at 9,744+ or other prod groups with 3 or more factors: the wall is steady across families (2–6
  uncovered at 9.4–9.7k after 20 min), so more time buys at most a few per cent.

## Files

- `scoreboard.jsonl`: one line per serious attempt (56 lines, 20 valid; score = vertices if valid, else uncovered count).
- `cands.txt`, `batch1.cmds`–`batch6.cmds`: exact commands. `run_one.sh`: single-run wrapper.
- `runs/`: logs of every run (and the solution files of the valid runs). `sols/`: valid solutions and checks.
- Binary: compile with `gcc -O3 -march=native -fopenmp -o haar_gen3 research/frontier/haar_gen3.c -lm` (not committed).
- Threads: at most 4 single-thread processes at a time (THREADS=1 each).
