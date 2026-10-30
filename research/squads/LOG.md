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
