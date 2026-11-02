### D = 13 at Δ = 5..10, second pass (job beyond-d13b, 2026-11-01/02)

Job beyond-d13b (Opus director + Haiku squad rounds, cloud session, branch claude/beyond-d13-extend-5n8uwl). Goal: raise
the D = 13 values of beyond-d13 at Δ = 5..10. Size cap for this job: 2N <= 3.0e10 vertices (the cap the coordinator
accepted for the 30-billion D = 11, 12 values of job beyond-d11b). Files: research/frontier/beyond13b/ (cells.txt lists
every value with its check; rows13b.py / splice13b.py put the rows and this section here; runs/ holds the solutions as
found and the haarcheck_gen logs, checks/ the metacheck and build_haar2 logs); squad cards and scoreboards
research/squads/beyond13b/r*; log research/squads/LOG.md.

<!-- RESULTS -->

**Method.** The same families as beyond-d13: Haar graphs H(G,S) of SL(2,p) x Z_n with alpha-orbit generator sets
(research/frontier/beyond11/haar_big0.c) at Δ = 6..10, and odd-order Frobenius groups Z_m x|_r Z_k with random S
(research/frontier/beyond13/meta/hmeta.c) at Δ = 5. What changed is how far up the size law the searches went: the
beyond-d13 values sat at mu = 7-10 (mu = N exp(-W/N), SIZE_LAW.md), found after 5-900 evaluations with cards running at
5-10 % of a core. Here the director ran the large cells on all four cores and the cards ran one thread each.

<!-- DETAILS -->
