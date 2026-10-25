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
