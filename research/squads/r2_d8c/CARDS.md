# Round 2 cards (own-d8-compound, 2026-10-26): strengthen the duality + pencil-coordinate family

Every card: read research/squads/r1_d8c/CONTEXT.md, then research/squads/r2_d8c/CONTEXT.md, then your card. Folder
research/squads/r2_d8c/cN/. Score as in r2 CONTEXT.md (largest m at q = 9 with sampled COST 0 on 3 x 64 sources).

## c1 Choose the axis
The weakness comes from points of H(9) on the axis Pi = a^perp cap a'^perp. Study how the choice of (a, a') changes
the degenerate structure and the cost: (i) the type of the line <a, a'> of PG(6,9) w.r.t. the quadric (secant,
tangent, external, totally singular; a or a' on the quadric or not); (ii) a, a' related to the duality (e.g. a' the
image of a under the collineation delta^2, or a, a' points of H(9) with delta-structure); (iii) random. For each,
record: #points of H(9) on the axis, #hexagon lines meeting the axis, #planes pi_p meeting the axis in a line, and the
sampled cost at m = 21, 26, 31, 36. Report the best axis and its scores.

## c2 Two axes and block layouts
Let beta_1 use axis Pi_1 and beta_2 use axis Pi_2 (independent pencil coordinates), and choose the images
B1 = f1(PG(1,9)), B2 = f2(PG(1,9)) in Z_m freely (not just [1,10], [11,20]): overlapping or partly symmetric blocks give
redundancy (a value that is in both B1 and -B2 is covered by a weak AND a strong route). For m = 26, 30, 33, 36, find
the layout with the lowest sampled cost; think first about which values are covered by which route sets (r2 CONTEXT).

## c3 Quadratic coordinates (pairs) for the weak blocks
A pencil coordinate collapses to one value on a line through the axis. A degree-2 coordinate, e.g.
c2(u) = Q'(u) / b(a,u)^2 or b(a,u) b(a',u) / b(a'',u)^2 (values in GF(9) u {inf}, mapped to Z_m), is 2-to-1 on most
projective lines and never constant on a line unless the forms are proportional there. Try: beta_1 = linear pencil
coordinate (strong blocks), beta_2 = quadratic coordinate (weak blocks), and other mixes. Measure distinct values of c2
on ideal lines (sample 1000 opposite pairs p, w: m1 = pi_p cap w^perp) and the sampled lift cost at m = 26..36.

## c4 delta and delta^-1 ('inv' mode) and delta composed with collineations
pencil_dual.py mode 'inv' uses the matchings p -- delta(p) and p -- delta^-1(p) (delta^2 is a nontrivial collineation for
q = 9). With delta^-1 the weak routes of the second matching go through the ideal lines pi_p cap (delta y)^perp and
pi_{delta y} cap p^perp, different from those of the first. Choose layouts where weak-only values lie in both images
(4 ideal lines must all fail) and measure m = 26..36. Also try p -- delta(g(p)) for a collineation g (e.g. delta^2).

## c5 Targeted repair
Take the m = 26 or m = 31 design (one axis, seed 1). From sampled sources, list the failing (source, target line,
offset) triples and their geometry (which ideal/hexagon lines are degenerate). Change the voltages of a few points
(start with the points on the axis, whose values are arbitrary, then points on degenerate lines) greedily or by a short
annealing whose cost is glift on 64 fixed sources; then evaluate on fresh sources (r:64:7, r:64:8) to check that the
gain generalizes. Report cost before/after on fresh sources and the number of points changed.

## c6 Any q, no duality: Pluecker pencil coordinates (q = 5 and 7)
For general q there is no duality. Use the guaranteed walks only: give points the pencil coordinate c(u) and lines a
pencil coordinate c'(L) computed from Pluecker coordinates (L spanned by x, y: p_ij = x_i y_j - x_j y_i; c'(L) =
[A.p : A'.p] for two fixed vectors A, A' of length 21; a planar pencil of lines is a projective line in the Pluecker
space, so c' is a bijection on every pencil that misses the axis). Choose a bijection sigma_t: P -> L that maps points
with c = kappa to lines with c' = kappa as far as class sizes allow (fill the rest arbitrarily) and give the edge
p -- sigma_t(p) the voltage f_t(c(p)); hexagon voltages 0. Theory (Opus): from p the lines through p carry the
offsets -f_t(c'(l)) (strong), the points of y carry -f_t(c(x)) (strong), so blocks -B1, -B2 are covered unless
degenerate; take symmetric blocks B_t = -B_t, m = 2q+3 (13 at q = 5, 17 at q = 7). Check exactly with glift at q = 5
(all sources) and q = 7 (r:64 then all if it passes). m = 17 at q = 7 would equal the lab's best annealed result with a
structured, explainable design.
