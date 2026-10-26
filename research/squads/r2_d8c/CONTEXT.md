# Squad round 2 of job own-d8-compound (2026-10-26): the duality + pencil-coordinate family at q = 9

Read research/squads/r1_d8c/CONTEXT.md first (problem, tools, machine rules, report format). This file adds the new
family found by Opus after round 1 and the goal of this round.

## The family (research/squads/cells/d10D8_work/pencil_dual.py)

q = 9 has a duality delta of H(9) (points <-> lines, incidence preserved): file
research/squads/r1_d8c/c5/dual9.phi (2N int32: delta(p) = phi[p] in N..2N-1 for points, delta(l) = phi[N+l] < N for
lines; verified: bijective, type-swapping, all 664,300 flags preserved). q = 3 has one too (dual3.phi, a polarity).
Base graph: I(H(q)) plus, for each point p, two parallel edges p -- delta(p) with voltages beta_1(p), beta_2(p) in Z_m;
hexagon voltages 0. Pencil coordinate: c(u) = [b(a,u) : b(a',u)] in PG(1,q) (two fixed vectors a, a'; b the polar form;
"axis" Pi = a^perp cap a'^perp; the ~q^3+q^2+q+1 points of H(q) on the axis have no value and get a random one).
Default voltages beta_1 = 1 + c, beta_2 = q+2 + c (blocks B1 = [1, q+1], B2 = [q+2, 2q+2]).
`python3 pencil_dual.py q phifile m seed OUT [same|inv]` then `glift OUT r:64:S` (sampled sources) or `all`.
GF(9) arithmetic: `gf_tables(9)` in pencil_dual.py (encoding of hexgen2.c, x^2+1).

## Why it works (Opus, proved route sets)

From a point p to a line y, write w = delta^-1(y). One-jump walks of length <= 7:
- jump at a point u (p ~> u -> delta(u) ~> y) exists iff d(p,u) + d(u,w) <= 6: offset +beta_t(u);
- jump at a line delta(z) (p ~> delta(z) -> z ~> y) exists iff d(delta^-1(p), z) + d(z,y) <= 6: offset -beta_t(z).
For p, w opposite, the first set is {p, w} u m1 u m2 with m1 = pi_p cap w^perp, m2 = pi_w cap p^perp: two "ideal"
lines (projective lines of totally singular planes, not hexagon lines). For delta^-1(p), y opposite lines, the second set
contains all points of the hexagon lines delta^-1(p) and y (these are the guaranteed families p -> l -> delta^-1(l) ~> y
and p ~> delta(z) -> z -> y). A pencil coordinate is a bijection onto PG(1,q) on every projective line that misses the
axis. So: the "strong" blocks -B1, -B2 are covered unless BOTH delta^-1(p) and y meet the axis; the "weak" blocks B1, B2
are covered unless both ideal lines m1, m2 meet the axis. Every plane pi_p meets the axis (a 3-space mapped onto F_q^2
has a kernel), so m1 is degenerate for about 1/q of the targets w; that is the weakness.
Checked: at q = 3 every predicted offset is reached (exact BFS); failures only in the degenerate classes.

## Measured at q = 9 (glift, 64 sampled sources, seed 3; one axis, seed 1)

m = 21 (strong blocks only would suffice if blocks were symmetric; here B1, B2 = [1,10], [11,20]): COST 132, 6 of 64
sources bad. m = 24: 23,859; 26: 36,845; 28: 56,208; 31: 81,062; 36: 166,260; 41: 381,875 (all 64 bad).
Table (12,8) = 35 copies of I(H(9)) (4,650,100 vertices). **Goal: m >= 36 at q = 9 with COST 0** (36 copies =
4,782,960 vertices beats the table). Intermediate goal: the largest m with sampled COST 0 on 3 x 64 sources.
At m = 41 all misses were in the weak blocks (+B1, +B2), in the classes (d(p,w), d(delta^-1 p, y)) = (6,6), (4,4),
(4,6), (6,4).

## Already tried (do not repeat)

Everything in round 1 (research/squads/r1_d8c/scoreboard.jsonl): random/annealed lifts, D7 levels, coordinate and
spread voltages, constant-shift duality matchings (Z10 lemma only), bilinear coordinate voltages with a duality
(best COST 22 at m = 12, q = 3), pair sheets, flag vertices, typed copies, hub surgery (+3.8% at q = 3).

## Scoring for this round

Score = largest m at q = 9 with COST 0 on `glift FILE r:64:1`, `r:64:2` and `r:64:3` (192 sampled sources). Report the
cost at the next m tried. Opus re-checks the best with all 132,860 sources. Each glift run on 64 sources takes about
0.5 s, so you can afford hundreds of evaluations; building a q = 9 base file with pencil_dual.py takes about 2 s (copy
it and modify; keep your generator in your folder). Time box: about 25 minutes. Machine: about 6 cards share 4 cores,
so OMP_NUM_THREADS=1.
