### D = 13 at Δ = 5..10, second pass (job beyond-d13b, 2026-11-01/02)

Job beyond-d13b (Opus director + Haiku squad rounds, cloud session, branch claude/beyond-d13-extend-5n8uwl). Goal: raise
the D = 13 values of beyond-d13 at Δ = 5..10. Size cap for this job: 2N <= 3.0e10 vertices (the cap the coordinator
accepted for the 30-billion D = 11, 12 values of job beyond-d11b). Files: research/frontier/beyond13b/ (cells.txt lists
every value with its check; rows13b.py / splice13b.py put the rows and this section here; runs/ holds the solutions as
found and the haarcheck_gen logs, checks/ the metacheck and build_haar2 logs); squad cards and scoreboards
research/squads/beyond13b/r*; log research/squads/LOG.md.

**Results.** (5..9,13): checked (haarcheck_gen, or metacheck + build_haar2 for the metacyclic group). (10,13): search
cost 0 and the (e,A) half of haarcheck_gen passed; the (e,B) half was stopped unfinished at the budget stop
(runs/d10D13_sl_601_67_orb3-3-1_s1.gen.partial.txt), so it is a candidate for the coordinator's check, not a table row yet.

| cell | was (beyond-d13) | now | gain | group, S | mu | found by |
|---|---:|---:|---:|---|---:|---|
| (5,13) | 3,594,910 | 3,729,966 | +3.8 % | Z32719 x\|_29509 Z57 (odd composite k), random S (hmeta) | 11.5 | r2/g03 (earlier 3,707,986, Z34981 x\| Z53, r1/f2) |
| (6,13) | 41,734,392 | 43,702,560 | +4.7 % | SL(2,89) x Z31, 2 free alpha-orbits | 18.8 | r1/e4 |
| (7,13) | 312,227,760 | 320,463,216 | +2.6 % | SL(2,163) x Z37, e + 2 orbits | 13.3 | r1/d2 (cost 2), closed by r2/g09 |
| (8,13) | 1,739,514,000 | 1,758,180,960 | +1.1 % | SL(2,359) x Z19, e + 1 fixed + 2 orbits | 9.3 | r2/g12 |
| (9,13) | 7,924,036,032 | 8,067,489,456 | +1.8 % | SL(2,677) x Z13, 3 free orbits | 14.1 | director |
| (10,13) | 19,980,294,768 | 29,088,880,800 (candidate, half checked) | +45.6 % | SL(2,601) x Z67, e + 3 orbits | 4.7 | director |


**Method.** The same families as beyond-d13: Haar graphs H(G,S) of SL(2,p) x Z_n with alpha-orbit generator sets
(research/frontier/beyond11/haar_big0.c) at Δ = 6..10, and odd-order Frobenius groups Z_m x|_r Z_k with random S
(research/frontier/beyond13/meta/hmeta.c) at Δ = 5. What changed is how far up the size law the searches went: the
beyond-d13 values sat at mu = 7-10 (mu = N exp(-W/N), SIZE_LAW.md), found after 5-900 evaluations with cards running at
5-10 % of a core. Here the director ran the large cells on all four cores and the cards ran one thread each.

**Per cell.**
- (10,13), director: the old value sat at the old 20-billion cap with mu ~ 0, so the gain is the cap itself. Group
  choice at 2N ~ 2.9-3.0e10 (lambda = W/N ~ 21.8): SL rather than PSL (one involution instead of ~p^2/2, each missed with
  probability ~exp(-lambda/2)), n odd and moderate (2n central elements, each missed with ~exp(-lambda/6)), and p <= ~620
  so that haarcheck_gen's p^2-entry field tables stay in cache and the check takes about an hour on 4 threads. SL(2,601) x
  Z67 (mu 4.7) reached cost 0 after 17 evaluations (175 s on 4 threads, 38 s per evaluation, 7.3 GB). Not tried:
  SL(2,607) x Z67 (2N = 29,968,823,424, mu 9.3), the largest p <= 620 shape under the cap (+3 %).
- (9,13), director: SL(2,677) x Z13 (mu 14.1) had stopped at cost 12 after a few evaluations in beyond-d13; in its own
  scheduling group it reached cost 0 after 113 evaluations (808 s).
- (8,13): SL(2,359) x Z19 (mu 9.3) solved in card r2/g12's first run. Near misses: SL(2,409) x Z13 (mu 11.6) at cost 2 in
  four runs (the two holes are an alpha-fixed inverse pair with z = 0, r2/g08), SL(2,461) x Z9 at cost 8.
- (7,13): SL(2,283) x Z7 (mu 11.2, 17 evaluations, r1/d1), then SL(2,163) x Z37 (mu 13.3): r1/d2 left it at cost 2 (the
  holes were -I on both sides), r2/g09 closed it by continuing the saved state with new seeds. At 2N ~ 3.2e8 the best
  cost fell with n: 12 (n = 21), 4 (n = 31), 2 then 0 (n = 37). PSL(2,163) x Z73 also solved (316,132,632, r1/d3).
- (6,13): SL(2,83) x Z37 and SL(2,89) x Z31 (mu 18.8) solved in 1-2 minutes (r1/e4), against mu 9.3 for the old
  PSL(2,83) x Z73. Larger n sat at constant costs (SL(2,67) x Z73 12, SL(2,61) x Z97 24, SL(2,59) x Z109 44, SL(2,47) x
  Z211 72); card r2/g08 showed these are frozen annealing, not an obstruction (below). Below the best but new shapes:
  orbits of size 5 (ORBIT "5 1 1", PSL(2,101) x Z41, 42,238,200, r1/e5) and a Frobenius group (Z342821 x| Z61,
  41,824,162, r1/e3). SL(2,277) x Z1 stayed at cost 2 in four runs (an alpha-fixed inverse pair).
- (5,13): single odd-order Frobenius groups Z_m x|_r Z_k with random S beat the old product of two Frobenius groups: up
  to mu ~ 10.7 they solve in 15-250 s, and they stall at cost 2 near mu 12-13.5 (Z35617 x| Z53, N 1,887,701). Continuing a
  saved cost-2 state with a new seed closed several near misses that fresh starts did not (Z42829 x| Z43, Z39199 x| Z47,
  a product, Z342821 x| Z61 at (6,13)). Composite odd k works (Z46411 x|_23265 Z39, 3,620,058); k = 21 does not.

**Hole anatomy at odd D (card r2/g08, research/squads/beyond13b/r2/g08/NOTE.md).** For S = alpha-orbits in
SL(2,p) x Z_n, the uncovered elements of a state are closed under Gamma = <alpha, x -> x^-1> on each side, so they come in
blocks of 6 (generic), 2 (an inverse pair of alpha-fixed elements) or 1 (-I). haar_big0 anneals on energy cost/3, so the
smallest generic move changes the energy by 2 and the chain freezes at its low temperatures (TMIN 0.15): the
constant-cost plateaus at (6,13) were 2-12 frozen blocks, not a forced obstruction (random symmetric S at SL(2,61) x Z97:
minimum 42 of 400, median 174). The alpha-fixed elements C(g) x {z : rz = z} are covered with probability
~exp(-lambda/3) and give a floor of about |C(g)| (mu/n)^(1/3) holes per side; that floor is what the small-n cost-2
states at (6,13), (7,13), (8,13) consist of.

**Process and what was left.** Two squad rounds of 16 Haiku cards (research/squads/beyond13b/r1, r2; a first launch,
r0, was aborted after four minutes because "remote" subagents ran in this container and collided). All cards and the
director share 4 cores; this kernel schedules by autogroup, so card runs were given an autogroup nice (bg.sh) to keep
the director's checks fast. Stopped at 01:10 UTC on 2026-11-02 by Doğa's budget stop, before round 3. Left: the (e,B)
half of the (10,13) check; SL(2,607) x Z67 (2N = 29,968,823,424, mu 9.3) for (10,13); (9,13) SL(2,599) x Z19 (mu 18);
near misses at cost 2-4 with saved states: (5,13) Z32833 x| Z57 (N 1,871,481), Z50321 x| Z37, Z43517 x| Z43, Z35617 x|
Z53; (6,13) PSL(2,101) x Z43 cost 15, SL(2,83) x Z39 cost 22; (7,13) SL(2,149) x Z49 cost 10; (8,13) SL(2,409) x Z13
cost 2, SL(2,461) x Z9 cost 8; and round 3's plan, re-annealing these with a higher final temperature (TMIN ~0.6),
since r2/g08 showed that haar_big0's default TMIN freezes odd-D searches on blocks of 6 holes.
