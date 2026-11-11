### D = 11 at Δ = 11..14 and D = 12 at Δ = 11..13 (job beyond-d11, 2026-11-01)

Job beyond-d11 (Opus director + four Haiku squad rounds of 16 cards, cloud session, branch
claude/new-cells-d11-d12-beyond-8sas9r). Seven new cells, and the D = 11, 12 values at Δ = 4..10 raised. Size limit
for the job: at most about 20 billion vertices, so that the low-memory checkers finish in a few hours.

**Method.** Haar graphs H(G,S), G = SL(2,p) x Z_n or PSL(2,p) x Z_n, S closed under alpha = (conjugation by a matrix
of order 3) x (z -> r z, r of order 3 mod n); research/frontier/beyond11/haar_big0.c is haar_big (64-bit, N/2 bytes,
bit-parallel BFS) plus two changes: f = 0 (S = free 3-orbits without e, evaluated as S s_0^-1; the right choice for
3 | Δ, so (12,11) and (12,12)), and a fix in the choice of alpha (haar_big took the first g with g^k = +-I, which for
k = 4, 6, 10 is an element of order 2 or 3; k = 3 and 5 were unaffected, so no earlier result changes). Every value is
checked by research/frontier/haarcheck_gen.c (own group code, BFS from (e,A) and (e,B)); logs in
research/frontier/runs/cloudcheck/<stem>.gen.txt, solutions in research/frontier/sols/.

**Even D was easy, odd D was not.** At D = 12 the first S solved at mu ~3 (one to five evaluations) and (11,12) solved
at mu 13.3 in 17 evaluations; (12,12) and (13,12) are limited by the 20-billion cap (mu ~ 0 there), not by the search.
At D = 11 the searches stall at cost 1-3 near mu 7-10, and the last holes are special elements. The reason
(research/frontier/beyond11/ODD_D_HOLES.md): for odd D = 2h+1 the same-side sets (S^-1 S)^h and (S S^-1)^h are closed
under inversion, so the words reaching an involution pair up, and the words reaching a central element are closed under
rotation (h rotations), and a central element is a hole on both sides at once. So involutions are missed with
probability ~exp(-lambda/2), central elements ~exp(-lambda/h), against exp(-lambda) for an ordinary element
(lambda = W/N ~ 19 here). PSL(2,p) has ~p^2/2 involutions, SL(2,p) only -I; G x Z_n has n or 2n central elements.
Hole counts of random S (squad card r2/d04) and a 22-group fit (r3/e14) agree with these rates within a factor 1.3-2.
Consequence used for every D = 11 value: SL(2,p) x Z_n with small n (1-43) and large p; PSL with n = 1 is the worst
shape at odd D (all ~130 holes per random S are involutions) although it is fine at even D.

**Squad (64 Haiku cards in 4 rounds; research/squads/LOG.md, research/squads/beyond11/r1..r4).** Round 1 mapped
structures and found the choose_alpha bug (two cards independently), the -I and torus near misses, and the size-law
calibration (mu ~7 within ~300 evaluations, ~10 within ~1,000). Round 2's hole anatomy (d04) explained the odd-D
failures; the director redirected seven running cards from PSL to SL mid-round, and four of them then raised cells.
Rounds 3-4 applied the rule to the cheap cells and raised (4..10, 11) and (4..10, 12) by 1-37 %. Cards that found
nothing: k = 2, 4, 5, 6 orbits at D = 11, self-dual (transpose-closed) S, annealing knobs, fixed-generator moves, -I as a
generator, a meet-in-the-middle near-miss finisher, composite n at (7,11).

**What failed or was not tried.**
- Pushing the odd-D cells past mu ~10: (12,11) SL(2,601) x Z7 (mu 10.7) stopped at cost 6, SL(2,193) x Z211 (mu 10.3) at
  cost 2 with -I its only hole; (11,11) PSL(2,257) x Z73 (mu 10.1) at 9; (11,12) PSL(2,241) x Z829 (mu 28) at 8.
- Near misses that stayed at cost 1-3 for thousands of evaluations: (6,11) SL(2,103), (7,11) SL(2,67) x Z19, (9,11)
  SL(2,137) x Z31, (6,12) PSL(2,211), (9,12) PSL(2,167) x Z241 and PSL(2,331) x Z31.
- (12,12) and (13,12) sit at the job's cap; larger groups would solve at once but their checks would exceed the
  checkers' budget (haarcheck_gen is memory-latency bound: the 14.4-billion-vertex (14,11) check took ~X CPU-hours).
