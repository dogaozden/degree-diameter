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
- 09:24 UTC: wave 1 finished, all four unsolved (5400 s each, seed 1):
  psl 13×217 best 27 (22.2·10⁶ evals); psl 17×97 best 12 (18.2·10⁶); psl 41×7 best 21 (12.7·10⁶); sl 17×49 best 18 (22.1·10⁶).
- The launcher script did not start wave 2 (it died while waiting). Wave 2 was started by hand at 09:25 UTC with the same
  j2_*.jobs files (3600 s each, ORBW=3, seed 2).
- 10:25 UTC: wave 2 finished, all unsolved (ORBW=3, seed 2, 3600 s): psl 13×217 best 27; psl 17×97 best 15;
  psl 41×7 best 15; sl 17×49 best 12. About 1.3·10⁸ evaluations over the eight runs so far, no run solved.
- Wave 3 (10:25 UTC, seed 3, RESTART=1, 3600 s): psl 17×97 and sl 17×49 with ORBW=5; psl 13×217 and psl 41×7 with
  ORBW=3 (j3_*.jobs, q3_*.out). A first version of the j3 jobs had k = 5 by mistake (Δ = 11); corrected before start.
- Current read: these candidates plateau at cost 12–27 (4–9 uncovered orbits) well before the record's μ = 38 solve
  point. The record's group needed 1.5·10⁶ evaluations; these have had 1–2·10⁷ each. If wave 3 also stalls, the
  cell is closed for this method at the orders tested.

## Conclusion (11:26 UTC, 3.5 h of the 6 h budget used)

Wave 3 (seed 3, RESTART=1, 3600 s): psl 13×217 best 27; psl 17×97 best 12 (ORBW=5); psl 41×7 best 18; sl 17×49 best 12 (ORBW=5). Nothing solved.

Total: 12 runs, about 1.6·10⁸ evaluations, on the four smallest-μ prime-field candidates above |G| = 231,420
(μ 47.9–56.4, k = 3, m = 2, f = 1). Every run plateaued at cost 12–27 (4–9 uncovered orbits) and never reached 0.
The record's group solved at μ = 38.2 in 1.5·10⁶ evaluations, so these are clearly harder, not just unlucky.

Decision: stop. Within this method (orbit-symmetric S, k = 3, f = 1, m = 2) and these groups, the (7,9) cell does not move
above 462,840 with our compute. Not tried, for the coordinator: a bigger model, SL(3,q) or other k = 5–7 structures
(STRUCTURE.md §7 item 3), or a voltage-lift route (research/lifts/, BEAT_16_5_SQUAD.md). Those are the options the
notes point to for the next step.

---

# Round 2 (job "raise2-7-9"): new notes, record 462,840 (|G| = 231,420)

Branch claude/raise-haar-d7d9-r2-mfd04e. Started 2026-10-25 from round 1's notes and LOG. The record is still
462,840 at the time of writing; nothing here is verified yet.

## What round 1 did not do, and why it missed these

Round 1 screened `orb_screen.py` with two limits that hid the best candidates in the window 231,421..237,000:

1. **n ≤ 400 and "every prime of n ≡ 1 mod 3"**. Any n with a prime ≡ 2 mod 3 or a factor 3 (so, e.g., Z_57 = Z_3 × Z_19)
   was excluded. A trivial action on a small factor of Z_n does not hurt in the samples (below), so this exclusion was too strict.
2. **Q prime only** in the family list (SL/PSL/PGL(2,p)), with Q = prime-power fields dropped from the product list. Round 2 uses
   `haar_sym`'s GF(p^k) support (sl 8, sl 16, psl 9, ...).

## Calibration on the candidates (k = 3, m = 2, f = 1; RANDORB, random symmetric S)

Record group for comparison: psl 29 × Z19 (N = 231,420, μ = 38.2, |Fix| = 14): min 42, p1 53, p10 93, median 227 (1000 samples).

| group | N | μ | |Fix| | min | p1 | p10 | median | note |
|---|---|---|---|---|---|---|---|---|
| sl 16 × Z57 | 232,560 | 40.1 | 44 | 34 (1000 samples) / 78 (300) | 105 | 190 | 625 / 567 | **new lead**: Z_3 acted on trivially |
| psl 17 × Z95 | 232,560 | 40.1 | 44 | 83 (1000) / 86 (300) | 100 | 168 | 523 / 514 | Z_5 acted on trivially |
| pgl 16 × Z57 | 232,560 | 40.1 | 44 | 95 (300) | 143 | 207 | 586 | (same order as sl 16 × 57) |
| psl 13 × Z215 | 234,780 | ~44 | 29 | 139 (300) | 161 | 291 | 1011 | 5 trivial, 43 ≡ 1 mod 3 |
| sl 8 × Z463 | 233,352 | 41.4 | 8 | 275 | 456 | 804 | 2580 | small Q, big Z: mixes badly (also k = 7, median 2608) |
| psl 11 × Z351, psl 13 × Z212, sl 11 × Z176, pgl 19 × Z34, psl 19 × Z68 | 231–233k | 38–40 | 53–2111 | | | | 6,800 – 360,000 | fixed points or trivial action too large |

Full 387-row screen of the window (all orders, prime powers, products, n ≤ 3000): runs in the scratch area, summarized above.

## k = 7 (m = 1, f = 0): not promising

The window has one order-7 candidate, SL(2,8) × Z463 (N = 233,352, μ = 41.4; SL(2,8) has order-7 elements with centralizer 7).
RANDORB with k = 7: min 788, median 2608, mean 1.9·10⁵ over 2000 random single orbits. Its mixing is much worse than the k = 3 record
group (small Q with large cyclic factor). Exhaustive k = 7 search is cheap (N/7 ≈ 33k orbits, about 2.5 min), but the
median says it would not find anything; not run.


## Run log (round 2)

- SL(2,16) × Z_57 (N = 232,560, μ = 40.05, |Fix| = 44, k = 3, m = 2, f = 1, α = conj(order 3) × z ↦ 7z): four
  seeds × 1200 s, one thread each (~2·10⁶ evaluations per run). Best costs 16, 16, 23, 23. **Not solved.** The record
  group reached 0 at 1.5·10⁶ evaluations, so this order is harder than the calibration suggested, not just unlucky.
- PSL(2,17) × Z_95 (same N, |Fix| = 44, α = conj × z ↦ 11z): four seeds × 1200 s launched next.
- Tooling note: a Monitor that waits with `pgrep -f <pattern>` matches its own command line and never exits. Wait on
  the RESULT line in each log instead.
- PSL(2,17) × Z_95 (N = 232,560, |Fix| = 44): four seeds × 1200 s, ~3.5·10⁶ evaluations each. Best costs 17, 17, 20, 26. **Not solved.**
- PSL(2,13) × Z_215 (N = 234,780, |Fix| = 29, 5 trivial, 43 ≡ 1 mod 3): four seeds × 1200 s launched next.
