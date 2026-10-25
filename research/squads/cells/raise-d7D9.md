# Raise (Δ, D) = (7, 9): notes for a fresh session

Job "raise-7-9" (Haiku worker, branch claude/raise-haar-d7d9-xec6c3, started 2026-10-25).
Goal: beat our record 462,840 = 2·|PSL(2,29) × Z19| (|G| = 231,420). Any Haar graph with |G| > 231,420 that
passes the diameter check is a new record. Stop after 6 h, or earlier if the cell is judged closed.

## Standing facts (from research/structured/STRUCTURE.md, §3–§4, §8; research/frontier/SIZE_LAW.md)

- Method: orbit-symmetric S with k = 3, m = 2 orbits, f = 1 (Δ = 1 + 3·2). Δ = 7 is not divisible by 3, so f = 0 does not apply.
- Group: Q × Z_n with Q = PSL(2,p) or SL(2,p) (SL for odd D is the memo's rule; PSL worked here at D = 9), every
  prime factor of n ≡ 1 mod 3, α = conjugation by an order-3 element × z ↦ r z.
- Command (what the record used): `ORBIT="3 2 1" ./haar_sym 7 9 SECS SEED 8 SOL psl 29 19`
  (record log: runs/d7D9_psl_29_19_orb3_s1.log: μ = 38.19, |Fix| = 14, solved at 1.5·10⁶ evals, 612 s, i.e. ~2400 evals/s on 1 thread).
- μ(N) = N·exp(−W/N) with W(7,9) from mu_plan.py; μ grows about like N^9.7 here, so each +1 % in N costs ≈ +10 % in μ.
- Calibration: RANDORB on the record group (2000 samples): min 42, p1 54, p10 95, median 228.

## Candidate orders just above 231,420 (orb_screen.py 7 9 231421 245000 "3 2 1")

Full table: runs/raise7_9/screen_7_9_231421-245000.txt. Chosen first rungs (prime p, sane fixed points, lowest μ):

| group | N | 2N | μ | |Fix| | RANDORB min / p1 / p10 |
|---|---|---|---|---|---|
| psl 13 × Z217 | 236,964 | 473,928 | 47.9 | 5 | 86 / 201 / 393 |
| psl 17 × Z97 | 237,456 | 474,912 | 48.9 | 8 | 60 / 108 / 195 |
| sl 17 × Z49 | 239,904 | 479,808 | 53.9 | 17 | 60 / 108 / 176 |
| psl 41 × Z7 | 241,080 | 482,160 | 56.4 | 20 | 48 / 95 / 147 |

Rejected: prod psl 3 × sl 5 × Z163 (N 234,720, μ 43.8) and prod psl 3 × sl 27 (μ 45.9): PSL(2,3) = A4 has a
quotient Z_3 on which the order-3 conjugation is trivial, and the random costs are 342+ and fixed points 17–161.

## Run log

- 2026-10-25 07:54: four 5400 s single-thread searches (orbq.sh, seed 1, K = 8), one per candidate above:
  runs/raise7_9/j_*.jobs, queue output q_*.out, logs and solutions in runs/raise7_9/.
- 08:50 UTC (t = 3330 s of 5400): all four wave-1 runs stalled. Best costs unchanged since t = 1830 s:
  psl 13×217: 44; psl 17×97: 12 (four uncovered orbits); psl 41×7: 21; sl 17×49: 18. Evaluations 8–14·10⁶ per run.
  The record run got from cost 6 to 0 at 1.5·10⁶ evaluations, so these candidates look harder than μ = 38 did.
- Wave 2 (runs/raise7_9/launch_wave2.sh, starts when wave 1 ends): seed 2, ORBW=3, 3600 s each, same four groups
  (j2_*.jobs, queue output q2_*.out).
