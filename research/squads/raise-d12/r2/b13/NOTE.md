# b13 idea: SL(2,8) x SL(2,8) x Z_19 with a diagonal field-type automorphism of order 3

Cell (6,12), Delta = 6, target 9,366,240 vertices (N = |G| > 4,683,120 needed).

Group: G = SL(2,8) x SL(2,8) x Z_19, N = 504*504*19 = 4,826,304, so 2N = 9,652,608 (a 3 % raise if it works).
Automorphism: sigma(x, y, z) = (F(x), F(y), 7z), where F is the Frobenius x -> x^2 of GF(8) acting entrywise
(order 3) and z -> 7z is an automorphism of Z_19 of order 3 (7^3 = 343 = 1 mod 19). Order 3, so orbits have size 3.
Fix(sigma) = SL(2,2) x SL(2,2) x {0}, 36 elements: small.
Why it is new: the two-factor product of a field group with a diagonal automorphism (no card covers it; b10 is
SL(2,8) x D_541 at (5,12), b02 is F_32768 x| C_151). G is perfect up to the Z_19 part, so G/[G,G] = Z_19 (small,
so the abelian-quotient wall should not bite).

Size law: W = sum over odd j <= 11 of 6*5^(j-1) = 60.9e6, W/N = 12.6, mu = N exp(-W/N) ~ 16 for a random S.
Orbit-closed S (two free 3-orbits, or e + one 3-orbit + two fixed points) should reduce the hit rate to roughly
exp(-mu/3) ~ 0.5 %. The test: RANDORB-style statistics of holes (uncovered B-vertices after radius 11) over
orbit-closed S, compared with unstructured random S at the same N, then annealing over orbit choices.

Check: BFS from (e,A) over the bipartite Haar graph H(G,S), 2N vertices, odd distances up to 11 must hit every
B-vertex. The solver is /home/user/degree-diameter/research/squads/raise-d12/r2/b13/haar_prod3.c.

## Results (round 2, card b13)
- Machine load ~19 on 4 cores: about 20 s wall per evaluation (about 0.7 s CPU), so only 24 evaluations in total.
- Two free sigma-orbits (mode T, 9 samples): holes 24, 31, 32 and 63+ (4 of 6 in the 63+ bucket on seed 7, 2 of 3 on seed 23).
- Annealing over orbit pairs (mode A, 4 moves): best 33.
- Unstructured random 6-sets (mode R, 4 samples): 7, 23, 30, 63+. Holes are not clumped by sigma, as the size law
  predicts for orbit-closed S (mu ~ 16 expected; observed much worse for orbit pairs).
- e + two Fix(sigma) points + one orbit (mode E, 7 samples): all 63+, best 15,939. The fixed points lie in the small
  subgroup SL(2,2)^2 x {0}, so they must not be used.
- No cost 0 found; nothing to verify. Idea looks weak at this size with random orbit pairs.
