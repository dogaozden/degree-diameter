### D = 14 raises at Δ = 3..7 and the new cells (9,14), (10,14) (job beyond-d14, 2026-11-01)

Job beyond-d14 (Opus director + Haiku squad rounds of 15-16 cards, cloud session, branch
claude/beyond-d14-new-cells-v6dcaa). The D = 14 column at Δ = 3..8 had been filled earlier the same day by job
beyond-d13; this job raised every cell at Δ = 3..7 and added (9,14) and (10,14). Files: research/frontier/beyond14/
(sols/, checks/, ownsmall/ for the lifts, census/ for the Foster census graphs); squad cards and scoreboards
research/squads/beyond14/r1..; log research/squads/LOG.md.

DRAFT - values and text are filled in at the end of the job.

**Δ = 3: regular lifts of tiny bases over Frobenius groups.** The lab's (3,10)-(3,12) records (job own-small) are
regular voltage lifts of 4+4 and 5+5 cubic bases over small non-abelian groups, with the base and the voltages annealed
together (salift_s). At D = 14 the same tool over Z113 x| Z7 (order 791, 4+4 base) gave 6,328 in a 60-s screen, a 3+3
base over Z47 x| Z23 (order 1,081) gave 6,486 (card r2/d04), and a 2+2 base over Z103 x|_8 Z17 (order 1,751) 7,004
(director, 40 CPU-seconds). The Foster census of cubic edge-transitive graphs (Potocnik et al.) has two semisymmetric
graphs of diameter 14 on 6,272 vertices, CSS(6272,3) and CSS(6272,7) (built from the census LCF notation, apsp VALID);
the beyond-d13 cyclic lifts stopped at 5,706.

Smaller bases reach a larger size-law mu: write the lift as a graph with N = p|G| vertices per side and
mu = N exp(-W/N), W = 16,383 cross-side words at Δ = 3, D = 14. Then the cyclic Pappus lift (5,706) sits at mu 9, the
census graph at 17, the 4+4 lift at 18, the 3+3 lift at 21 and the 2+2 lift at 33 (the lab's (3,12) 4+4 record is at
37 by the same count). The 1+1 case is a cubic Haar graph H(G,{e,x,y}); for a Frobenius group Z_m x| Z_k almost all of
its automorphism group (order m(m-1)) acts on the pairs (x,y), so there are only about k^2 different graphs per group,
which is why exhaustive cubic Haar searches stop far lower (5,040 at D = 14). A 2+2 base has three free voltages after
fixing a spanning tree, in a group half the size, and several base shapes; the 7,004 solution's base is a 4-cycle with
two opposite edges doubled.

**Δ = 4..7: Haar graphs, pushed further.** Same families as beyond-d13, larger groups, and one new orbit form.
- (4,14): metacyclic groups Z_m x| Z_k with m prime and random S (hmeta), screened 20 s each over every such group in
  an order window, then chained: Z3079 x| Z81 (498,798, r1/c05), Z5849 x| Z43 (503,014, r2/d07). Products of two
  Frobenius groups, PSL/SL/PGL/AGL with random S, and order-2 orbit forms did not do better.
- (5,14): two routes passed the old 12,795,166: an order-2 orbit form in PSL(2,163) x Z3 (S = {e, x, ax, y, ay}, a an
  involutive automorphism; 12,991,752, r1/c11) and metacyclic random S, Z152393 x| Z43 (13,105,798, r1/c08, found in 4
  seconds at mu 7.7). The order-2 form failed in SL(2,q) x Z_n (cost 18-36) and in metacyclic groups (cost ~4,000).
- (6,14), (7,14): the beyond-d13 forms ("3 2 0", "3 2 1" in SL/PSL(2,p) x Z_n). The new observation is that at D = 14
  a random symmetric S often has cost 0 outright: SL(2,137) x Z37 at the first random S (mu 10.3), and RANDORB screens
  (8-30 random symmetric S per group) found cost 0 in about 1 S in 8 at (7,14), N = 854M (mu 9.3). Other orbit forms
  ("6 1 0", "2 3 0", "3 1 3" at Δ = 6; "2 3 1", "6 1 1" at Δ = 7) were much worse.

**Δ = 9, 10: new cells.** H(PSL(2,241) x Z1429, S) with S three free alpha-orbits of size 3 has 20,002,113,120 vertices
and diameter 14 ...
