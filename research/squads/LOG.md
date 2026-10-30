# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-30, job d75-raise (Opus cloud session), goal (7,5) > 1,200, round d75-r1 (14:40-15:40 UTC)

Cards (scoreboard `d75-r1/scoreboard.jsonl`, rules `d75-r1/COMMON.md`): c1 Haar graphs of order-640 groups with
fewest involutions (symmetric S) · c2 tabu over non-symmetric S at SmallGroup(605,4) · c3 4-vertex-base lifts with
alpha-invariant voltage classes, orders 301-330 · c4 non-Haar bi-coset graphs |H| = 2 at the many-group orders
1216-1312 · c5 symmetric Haar graphs, orders 661-720 · c6 Haar S = union of cycles of an affine map g*alpha(x) ·
c7 wildcard: bi-coset |H| = |K| = 3 of odd-order groups 1809-1911 · c8 wildcard: Z3-symmetric 3+3 lifts (= Haar of
K:Z3), plain annealing.
Best per card (cost = uncovered elements or vertices; no card found a valid graph): c1 20 (1280, 640_3, annealing;
exhaustive symmetric: no set passes the first half) · c2 2 (1210) · c3 96 (1248) · c4 24 (1260, SmallGroup(1260,74)) ·
c5 no symmetric set passes the first half in 41+ groups of order 663-700 · c6 2 (1210; re-finds the 1,200 graph) ·
c7 10 (1210) · c8 4 (1218, SmallGroup(609,1); unreproduced).
Kept / learned: calibrations matter. Plain annealing (haar75 sa, 30 s) does not re-find the 1,200 graph (c1), and
tabu over free 4-vertex-lift voltages does not re-find the 1,152 graph as a lift of A4 x C24 / S4 x C12 (director,
90 s: 10-17). So at Delta = 7 local search is not a reliable tool; exhaustive structured enumeration is.
What happened next (director, not the squad): the 1,200 record's S turned out to be self-dual (an automorphism beta
inverts every element of S; another gives psi(x) = beta(x)^-1 with orbits {e} + 3 pairs). Sets invariant under such a
psi make the Haar graph colour-swapping-symmetric, so only half the diameter test has to pass. The exhaustive search of
that family (haar75 anti) found 1,204 (602,2), 1,210 (605,6) and **1,240 (620,1) = new record** within minutes. The
squad round did not find it, but its negative results (all symmetric/annealing routes at 1,210+ stuck at cost 2+)
are what pushed the director to look at the record's own structure.

## 2026-10-30, job d75-raise, round d75-r2 (15:37-16:20 UTC), goal (7,5) > 1,312

Context: the director had just found 1,240 and 1,312 with self-dual Haar sets (haar75 anti). Round 2 generalised the
self-dual (colour-swap) idea in 8 directions (rules `d75-r2/COMMON.md`, scoreboard `d75-r2/scoreboard.jsonl`):
c1 self-dual bi-coset graphs |H| = 2 · c2 self-dual 4-vertex-base lifts · c3 pattern mining + formula-only search of
metacyclic C_p : C_k · c4 annealing/tabu inside the capped self-dual types · c5 doubly symmetric (alpha- and
psi-invariant) sets at orders 701-800 · c6 self-dual bi-coset |H| = 3 · c7 wildcard: psi(x) = beta(x)^-1 w with w != e ·
c8 self-dual Haar sets on hand-built families (C_p : C_k with central kernels, SL(2,3) x C28, ...).
Best per card (no card found a graph above 1,312): c1 0 solutions on C73:C18 (1,314) and C74:C18 (1,332); tool
calibrated (720 unions on SmallGroup(1200,475), as bic75) · c2 cost 13 (1,344, C7:C48); calibrated at (5,5) (valid 384) ·
c4 tabu re-finds the 1,312 and 1,240 solutions in 60 s (the first local search that passes a Delta = 7 calibration);
(5,1) looks structurally poor (best 207 on 656_28); capped types at 680-696: 58+ · c7 cost 10 (1,314); not calibrated ·
c8 8 new groups (664-716, 672:747), 0 solutions.
c3 pattern: in all three metacyclic hits G = C_p : C_2d (y^d central) and beta = (x -> x^-1, y -> y^v), v in {1, 1+d};
formula-only dd_meta.c (calibrated: 18/18 solutions on 656_28) shows no metacyclic C_p : C_2d of order 661-800 has a
solution (complete) · c5 doubly symmetric sets, orders 701-800 (e.g. 756): best cost 231+ · c6 self-dual bi-coset
|H| = 3, |G| = 1971-1998: no solution.
Kept: c4's tabu (calibrated inside the self-dual family), c1's self-dual bi-coset tool, c3's pattern and dd_meta. The
director's own sweep then showed order 672 (1,344 vertices) is "warm": many groups C7 : (2-group x C3) with 3
involutions miss by only 4-6 elements (672_22, 672_34: 4), so the remaining CPU went to all order-672 groups with
<= 7 involutions. Round 2 added tools and negatives but no graph; no round 3 (two rounds without a new graph).
