### D = 11 raises at Δ = 5..12 and 16 (job raise-d11, 2026-11-01/02)

Job raise-d11 (Opus director + Haiku squad rounds, cloud session, branch claude/raise-d11-frontier-26r11l; notes in
research/frontier/raise11/RAISE11.md, squad log in research/squads/LOG.md).

**The lever: small n.** The earlier D = 11 jobs used SL(2,p) x Z_n with n up to 271 (and PSL with n = 1) and stalled at
size-law mu ~ 7-11. Squad card r1/c13 wrote a clump model (research/squads/raise11/r1/c13/MODEL.md): with S closed
under alpha (order 3) the holes come in clumps, generic elements 6 at a time (alpha x inversion), alpha-fixed torus
elements (about p of them, missed with probability ~exp(-lambda/3)) and central elements (+-I, z) (2n of them,
~exp(-lambda/5)) singly or in pairs; K = expected number of independent clumps, P(cost 0 per fresh run) ~ exp(-K).
Ranking groups by K (research/frontier/raise11/rank11.py) picks SL(2,p) x Z_n with n = 1..31; those solved at
mu ~ 15 within a few fresh runs. Fresh seeds beat resumed chains near the limit.

**Values (all independently checked):**
- (5,11) 311,942: Frobenius Z8209 x|_477 Z19 (haar_meta, squad r3/f10; metacheck + build_haar2.py).
- (6,11) 2,135,280: PSL(2,41) x Z31, ORBIT "3 2 0" (r2/e09; haarcheck_gen + haarcheck_lean). The orbit search now beats
  the Frobenius family at Δ = 6 (also found: 2,124,866, Frobenius Z25913 x| Z41, r1/c01).
- (7,11) 11,426,448: SL(2,67) x Z19 (r3/f01; haarcheck_gen + haarcheck_lean); also 11,311,584 PSL(2,47) x Z109 (r1/c04).
- (8,11) 46,547,568: SL(2,107) x Z19 (r4/g02); also 46,309,200 SL(2,149) x Z7 (r1/c06, the model's first pick).
- (10,11) 469,768,992: SL(2,617), director seed loop; also 461,335,200 SL(2,151) x Z67 (r1/c08).
- (12,11) 3,039,136,800: SL(2,601) x Z7, f = 0, director, 5 evaluations (haarcheck_gen 3,781 s).
- (16,11) 33,763,363,200: PSL(2,449) x Z373, first random S (the old value 29,961,590,400 was the beyond-d11b job's
  30-billion cap; mu ~ 0 here); see the check note in the table row.

**What did not work (details in RAISE11.md):** inverse-closed S (S = S^-1, one side to cover: per-side holes double
without e, words collapse with e; haar_sd.c, card r1/c12); more alpha-fixed generators (f >= 4); PGL, SL(2,49), AGL(1,q)
at (7,11) (r1/c15); pure random sampling instead of annealing (r2/e13); rungs with model K above ~9-10 did not solve
in 10-15 fresh runs per card. (9,11) and (11,11), (13,11), (14,11) were not raised: their best groups reached cost 2
(9,11 SL(2,137) x Z31, +2.68 %) or 6-12 under the job's CPU budget.

**Machine lessons:** the bash cgroup is limited to 14.3 GB, so checks of 12+ GB need a quiet window; autogroup
scheduling makes `nice` inside card shells useless (renice_loop.sh sets autogroup nice per process); with ~20
concurrent searches on 4 cores a single evaluation was 20-25x slower than on an idle core (cache and memory-bandwidth
contention on top of the CPU share), so rounds of 16 cards lost throughput; rounds 3-4 used fewer concurrent searches.
