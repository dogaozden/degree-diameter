# raise-d8D9: beat the (8,9) record of 1,326,960 vertices

Job "raise-8-9" (Haar worker, Haiku 5.5, 2026-10-25). Branch: claude/raise-d8d9-record-ogr1zr.

## Target and arithmetic
- Current record: Haar graph of SL(2,19) x Z_97, N = |G| = 663,480, 2N = 1,326,960 (research/frontier/sols/d8D9_sl_19_97_orb3_s2.txt).
- To beat it: a valid Haar graph with N >= 663,481 (2N >= 1,326,962). Check: a checker output with vertices > 1,326,960.
- W(8,9) = 6,725,601 (odd D formula, research/structured/tools/mu_plan.py). mu = N exp(-W/N).
  - record: mu = 26.3. N = 670k: mu = 29.3. N = 680k: mu = 34.4. Each +1 in mu is roughly +0.3 % in N.
- Candidate groups in [663,481, 690,000] with mu <= 30 (from `orb_screen.py 8 9 663481 690000 "3 2 2" --list`):
  sl/pgl 16 x 163 (665,040, mu 27.0), prod sl 8 x sl 11 (665,280, mu 27.1), prod psl 3 x psl 7 x 331 (667,296, mu 28.0),
  prod psl 5 x psl 9 x 31 (669,600, mu 29.1), sl 13 x 307 (670,488, mu 29.5), pgl 25 x 43 / sl 25 x 43 (670,800, mu 29.7).

## Method
- Orbit search (research/structured, haar_sym), ORBIT="3 2 2": k = 3 automorphism, 2 free orbits + 2 fixed generators.
  That is d = 2 + 3*2 = 8. The k = 3 family produced most D = 9 records.
- Screening: `tools/orb_screen.py 8 9 663481 690000 "3 2 2" --samples 2000` ranks groups by the lower tail of random-S cost.
- Verification: build_haar2.py (<= 20M vertices). Every candidate must pass before it goes into research/frontier/sols/.

## Runs
- Speed: about 350 evals/s per core at N = 670k (sl 13 x 307, haar_gen3 evaluation). prod sl 8 x sl 11 uses wide rows.
- b1 (research/frontier/runs/raise-d8D9/b1): prod sl 8 x sl 11 x Z1, 3600 s, seed 1, in progress.

## Status
- In progress. No new record yet.

## Progress log
- 07:49 start b1 (seed 1), b2 (seed 2): prod sl 8 x sl 11 x Z1, ORBIT "3 2 2", 3600 s each. b3: sl 16 x Z163, seed 1.
- ~1500 s: b1 best cost 5 (1.88M evals), b2 best cost 5 (1.76M), b3 best cost 9 (1.79M). Not solved yet.
- Group screen (random-S tails, samples 2000) is still running at this point.
- Group screen finished (research/frontier/runs/raise-d8D9/screen/screen_k3f2m2.txt, columns: N, mu, |Fix|, min, p1, p10, median of random-S cost).
  Top by p1 (lower is better): psl 47 x Z13 (p1 51, mu 31.5); prod sl 8 x sl 11 (p1 52, mu 27.1, |Fix| 107);
  sl 25 x Z43 (p1 54, mu 29.7); pgl 25 x Z43 (p1 60, mu 29.7); prod sl 4 psl 9 x Z31 and prod psl 5 psl 9 x Z31 (p1 ~80, mu 29.1).
  sl 16 x Z163 ranks 9th (p1 99) despite the lowest mu. psl 47 x Z13 already reached cost 6 in 2400 s earlier (research/structured/runs).
- ~1800 s: b1 best 5, b2 best 5, b3 best 9. Still none solved (runs end at 3600 s, about 08:49).
- Next candidates to run after these: sl 25 x Z43 and psl 47 x Z13 (longer), then more seeds on the best group.

## RECORD: (8,9) 1,330,560 vertices (beats 1,326,960 by 3,600)
- Group: PROD sl 8 (poly x^3+x+1) x sl 11, Z_1; N = |G| = 665,280; 2N = 1,330,560. Orbit search ORBIT="3 2 2", seed 2, K=8,
  3,094,273 evals in 2,630 s (run b2, research/frontier/runs/raise-d8D9/b2/).
- Solution: research/frontier/sols/d8D9_prod_sl_8_sl_11_1_orb3_s2.txt (sha256 of the edge list 15d7aa6b6662c7a3aee6d936f39b7b00e70a145fb8e27c790a6c4143b56f15b9).
- Checks: haar_sym full diameter check (OK); build_haar2.py VALID d=8 D=9; research/frontier/check_haar_indep.py VALID
  (BFS from A and B: ecc 9, reached all, 8 distinct neighbours each). Log in the same folder.
- mu = 27.1 with |Fix(alpha)| = 107. The fixed-point term was large, and it still solved.
- Still running: b1 (same group, seed 1), b3 (sl 16 x Z163), b4 (sl 25 x Z43). Next: push this group further (more seeds, larger order).
