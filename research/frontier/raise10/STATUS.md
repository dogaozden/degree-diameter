# raise-d10: status at stop (2026-11-02 01:08 UTC, stopped by Doğa for budget)

## Found and independently checked (hcheckpsl, BFS from (e,A) and (e,B), ecc 10/10)

| cell | new value | was | group, S | evals | check log |
|---|---:|---:|---|---:|---|
| (17,10) | **7,832,948,760** | 7,022,052,336 | PSL(2,181) x Z1321, e + 1 fixed + 3 orbits of size 5 ("5 3 2", FIXF), mu 29.2 | 598 | checks/d17D10_psl_181_1321_orb5-3-2_s1.hcheckpsl.txt |
| (18,10) | **12,784,852,920** | 11,787,972,672 | PSL(2,211) x Z1361, "5 3 3" FIXF, mu 17.6 | 21 | checks/d18D10_psl_211_1361_orb5-3-3_s2.hcheckpsl.txt |
| (19,10) | **20,785,224,720** | 19,233,722,496 | PSL(2,311) x Z691, "5 3 4" FIXF, mu 17.4 | 46 | checks/d19D10_psl_311_691_orb5-3-4_s2.hcheckpsl.txt |

Solutions: ../sols/d17D10_psl_181_1321_orb5-3-2_s1.txt, d18D10_psl_211_1361_orb5-3-3_s2.txt, d19D10_psl_311_691_orb5-3-4_s2.txt.

## Found, NOT yet checked

- (20,10) **33,036,831,960** (was 30,518,778,360): PSL(2,331) x Z911, S = 4 free orbits of size 5 (f = 0), found by haar_big1
  (this job's FIXF extension to f = 0) in 9 evaluations, search re-evaluation cost 0. Solution: runs/d20D10_psl_331_911_orb5-4-0_s1.out.
  The hcheckpsl check (needs ~8 GB, ~45 min on 2 threads) was stopped after 38 minutes, unfinished. Run:
  `THREADS=2 ./bin/hcheckpsl runs/d20D10_psl_331_911_orb5-4-0_s1.out` (or chk.sh).

## Negative / exhaustive results

- exh4 (exh4/exh4.c, exhaustive over all S = {e,x,y,z} up to automorphisms, validated on the incumbent's group): **none of the
  39 Frobenius groups Z_p x| Z_k of order 6,209-6,600 has a Haar graph with Δ = 4, D = 10** (best minimum: Z251 x| Z25, cost 2).
  Of the 23 groups Z_p x| Z_k with r of order k/2 (central involution, like the (4,10) incumbent), 6 were done (none) when stopped
  (exh4/sweep_half.log).
- Squad (4 rounds, 65 Haiku cards; research/squads/LOG.md): no raise of (3..8,10). Near misses at cost 1-3: (5,10) Z1453 x| Z33
  (cost 1, a strict 1-opt local minimum), A4 x (Z239 x| Z17) cost 1; (6,10) Z6397 x| Z41 cost 1 (strict 1-opt minimum);
  (4,10) (Z7 x| Z3) x (Z43 x| Z7) cost 3; (3,10) Heawood x Z58 lift cost 6.

## Left when stopped (states in runs/*.out.best, resumable with START=)

- (13,10) PSL(2,179) x Z121 "5 2 3" FIXF, mu 31.3 (+1.46 % if solved): cost 5 after 2,395 evaluations.
- (12,10) PSL(2,131) x Z151 "5 2 2" FIXF, mu 39.2 (+2.0 %): cost 5 after 3,386 evaluations.
- (10,10) haar_big1 PSL(2,79) x Z131 "5 2 0" FIXF, mu 44.3 (+0.44 %): cost 10 after 3,108 evaluations.
- (18,10) push: PSL(2,251) x Z821 "5 3 3", mu 24.1 (+1.55 % over the new value): cost 5 after 307 evaluations.
- Lesson for the next run: with k = 5 orbits and the FIXF screen, the Δ = 17..20 cells solved at mu 17-18 in 9-46 evaluations
  and at mu 29 in ~600; the mid cells (12..14,10) at mu 31-39 were still at one orbit (cost 5) after 2,400-3,400.
