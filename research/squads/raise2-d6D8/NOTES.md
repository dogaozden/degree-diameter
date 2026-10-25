# raise2-6-8 notes (Haiku worker, round 2 of job "raise-6-8")

Goal: beat the (6,8) record 31,680 vertices = 2N with N = 15,840 (psl 11 x Z24, ORBIT "2 3 0").
Any Haar graph with N >= 15,841 is a new record. Round 1 (branch claude/raise-d6d8-haar-qyrz7g) ran k=2 orbit
searches on sl/psl/pgl x Z_n groups of order 16,128..18,216 (plateau cost 8..26) and stopped. Read its
research/squads/cells/raise-d6D8.md first. Round 1 said heis/meta/csl/tpgl "need new code": WRONG for heis and meta
(research/structured/haar_sym.c parses them). csl/tpgl are plain-only (ORBIT refuses them), so they are out here.

## Setup
- Tool: research/structured/haar_sym.c (built with gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm).
- Baseline check (this session): `ORBIT="2 3 0" THREADS=1 ./haar_sym 6 8 60 1 8 out.txt psl 11 24` solved at 46.6 s, 2.7e6 evals.
- Screen: squads/raise2-d6D8/enum_groups.py (sl/psl/pgl x Z_n, agl1 x Z_n, heis x Z_n, meta m k r with k <= 60)
  and screen_run.py (RANDORB random-sample statistics, 2000 samples, ~0.1-0.6 s per group).
- Heisenberg groups screened badly (heis 5 x Z127: min 8,817 of 2000 samples; random S mean ~11,000): not used.

## Counting (why this window might still be open)
- W(6,8) = 97,656 (words of length <= 7 counted by the tool), mu(N) = N exp(-W/N): mu(15,840) = 33.3, mu(16,000) = 35.7,
  mu(16,500) = 44.3, mu(17,000) = 54.6.
- Random-model count of cost-0 orbit sets for k=2, m=3: options ~ (N/2)^3/6 ~ 8.5e10; P ~ exp(-mu/2): expected
  solutions ~ 5e3 at N = 15,840, ~1.4e3 at 16,000, ~20 at 16,500. The random model says solutions should exist; the
  round-1 plateaus say group structure, not counting, is the obstacle.

## Log
(append below: time, what ran, result)

- 14:45 full k=2 screen on 9,802 specs (groups_15841_17000.txt -> screen/k2_full.tsv), 4 workers, 2000 samples.
- 14:50-14:54 wave 1 (meta, ORBIT "2 3 0", seed 1, stopped at ~240 s to free cores): meta 1223x13 r117 (N 15899) best 11;
  meta 1223x13 r236 (15899) best 11; meta 953x17 r16 (16201) best 12; meta 1453x11 r69 (15983) best 18. Evals ~8k/s (generic
  evaluator: no cyclic subgroup of order >= 64), 1.4-2.4M evals at stop. The control reached best 2 at 1.8M evals.
  Verdict: the metacyclic candidates that the k=2 screen liked plateau at 11-18. The random-sample screen does not predict them.
- k=2 screen (screen/k2_full.tsv, 3,739 specs with N <= 16,290): best screen scores (p1+p10)/2 are the metacyclic
  ones at 51-52 (meta 1223x13, N 15899) against 48 for the control; every sl/psl/pgl x Z_n candidate with k=2 is worse
  (psl 7 x Z_n: 170-600). The rest of the window (N 16,290..17,000, 6,300 specs, mostly meta with k up to 60) was not
  screened: at 30 specs/min the run was too slow, and the tail base families were screened separately (screen/k2_tail_base.tsv).
- k=3 screen on base families (screen/k3_base.tsv, ORBIT "3 2 0"): PSL(2,7) x Z_n is competitive only at k=3:
  psl 7 x Z95 (N 15960, a new record size if solved) min 12 p1 25 p10 76 (score 50.5); sl 7 x Z49 (16464) score 51;
  psl 7 x Z98 (16464) min 6. Random-model count for psl 7 x Z95 at k=3: options (N/3)^2/2 = 1.4e7, mu/3 = 11.7,
  expected cost-0 sets ~100 (k=2 with mu/2 = 16.6 has ~5000 expected at N=15,840, so the counts are not comparable
  across k; this is only a rough guide).
- 14:54-15:09 wave 2 (k=3, ORBIT "3 2 0", 900 s, 54M evals each, seed 1 or 2): psl 7 x Z95 (15960) best 11 (both seeds);
  psl 7 x Z98 (16464) best 6; sl 7 x Z49 (16464) best 3. No solution. Plateaus form in ~1-2 min and do not move.
- 15:09-15:26 alpha sweep for sl 7 x Z49, k=3: the tool does NOT reject an invalid ALPHA (it prints "alpha^k != 1" and
  carries on), so the first sweep was garbage. Valid = conjugating matrices x in SL(2,7) with x^3 = +-I (112 of 336; see
  alpha_valid.py, alpha_sweep_k3/valid_k3_sl7.txt). 5000 random samples per valid alpha: min 3 at the best alphas
  (p1 27-30), all alphas similar. Wave 3 (900 s, ALPHA = 120, 265, 141, 170): all four plateau at exactly 3 after 55M evals.
  Cost 3 from four different alphas and default alpha suggests a structural floor for this group, not a bad alpha.
  (Not verified: which 3 elements stay uncovered. A diagnostic would print the uncovered set at the plateau.)
- Note for the k=3 family: the orbit construction needs an order-3 automorphism on Z_n, so n must have a prime
  factor 1 mod 3 (or 9 | n). Orders 96, 99, 100 in the window are degenerate for k=3 (cost 12,000+).
- Round-1 check: the random-model count said k=3 solutions should exist at N = 15,960 and 16,464 (about 100 and 7 expected).
  The annealing says otherwise. The count is only a guide: its per-element independence assumption is clearly wrong
  for these groups, and it was also badly off for the k=2 groups in round 1.
