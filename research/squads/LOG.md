# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 ~14:20–14:45 UTC, cell-10-5 resume (session_01NTgHArireuhKVofyqgzKgX), goal (10,5) > 4,820, round 1

Context: the 4,800 DM lift of W(7) plus "hubs" (freed point–line pairs, +4 vertices each) had given 4,804 and 4,820
(5 freed flags) before the round. Cards (research/squads/d10D5/r1/, scoreboard.jsonl):
- c1 local search (SA in C) over flag sets for a perfect exact-coverage matching: k = 6 found in ~10 s; coset-0 stuck at 7.
- c2 relaxed coverage (matching deficiency 2, σ completed, BFS annealing): k = 6, best cost 16, no valid graph.
- c3 non-flag freed pairs (per-pair g, g'): k = 6 flags exact; non-flag mixes ≤ 4; coset-0 stuck at 15.
- c4 hub-graph patching of holes: k = 6 with feasible hub graph; coset-0 stuck at 29.
- c5 symmetric flag sets: **k = 8** flags with a perfect exact-coverage matching, one orbit of a semiregular order-8
  element of PGSp(4,7) (8 collinear point pairs, 8 concurrent line pairs). Its run failed on the hub graph (old
  common-neighbour rule) and coset-0 (8 pairs).
- c6 slack in the 4,820 graph: only 4 spare degree units; no vertex can be added; edge surgery fails. Negative.
- c7 other constructions: GQ(7,9) = T2*(O) Z6 lifts dead (581,923 bad pairs, structural); Z7/Z8 DM on W(7) ~2.4% per
  pair. Negative.
- c8 Hall-obstruction theory: the violator is a point collinear with three freed points off their lines whose
  freed lines have no common transversal (point triads have 1 or 8 centres, disjoint-line triads 0 or 2 transversals);
  a pair/triple-condition sampler finds 7 exact flags in 12 s, 8 not in 300 tries; coset-0 stuck at 4.
Kept: c5's orbit flag set (k = 8) and c1's fast flag search. My own changes during the round: a hub-graph rule that
counts z_i ~ z'_m as linking z_i to both hubs of p_m (p_m on l_m), so 2 edges per flag pair suffice and up to 9 flags
fit (out/in-degree ≤ 4 tournament); hub-graph "patch" edges for coverage holes; relaxed coverage (routes, not exact
matching) found σ for 6 flags quickly. Everyone ended blocked on the coset-0 annealing (6..29 bad pairs).
Outcome after the round (Opus): the targeted coset-0 route move (σ(v), σ(u) of a bad pair made to meet) plus a short
hot polish turned c5's 8-flag orbit into a VALID **4,832** (research/squads/d10D5/hubs/checks/d10D5_n4832_CHECK.md).
Verdict: the round helped decisively (c5's symmetric set is the record's skeleton; c8's theory explains the k ≈ 7
barrier for unstructured sets; c6/c7 closed two side routes).

## 2026-10-25 ~14:50–15:15 UTC, cell-10-5 resume (session_01NTgHArireuhKVofyqgzKgX), goal (10,5) > 4,832, round 2

Five cards (research/squads/d10D5/r2/, scoreboard.jsonl), all aimed at k >= 9 freed flags:
- c1 order-9/10/12 orbits: order-10 semiregular elements give 0 feasible 10-orbits; order-5 single orbits feasible
  (360) but no feasible pair; the 8-orbit has no exact one-flag extension (best 395/400). No graph.
- c2 8-orbit + one flag with relaxed coverage: 3 unpatchable holes remained (hub graph not co-designed). No graph.
- c3 triad sampler / C local search for 9 flags: deficiency 5; produced a second VALID 4,828 (k = 7, c8's set),
  confirming the pipeline. No record.
- c4 mixed hub counts (HLIST): per-flag hub numbers implemented; hub-sourced cost 0 at k = 10 by BFS. Its capacity
  model (common neighbour / one hop) is superseded by the exact hub-distance rule below.
- c5 unions of order-4/5 orbits: all 6,960 disjoint pairs of feasible 5-orbits have deficiency >= 20. No graph.
Kept: c1's best 9th flag (19:139). Opus during the round: same-side hubs only need distance <= 4, and a path of length
4 inside the hub graph counts, so a degree-4 bipartite hub graph of diameter 4 (up to 40 + 40 hubs, e.g. the incidence
graph of GQ(3,3)) removes the hub limit; hub edges also give coverage routes ((p_i,0) -> z_i -> z'_j -> (l_j) -> points
of l_j). dmhub now builds the hub graph first (exact distances), fills spare degree, and anneals sigma and hub edges
jointly against coverage-with-hub-routes. With c1's 9th flag this gave coverage 0 in ~2 minutes, then dmfast_hub with
the same hub graph and a hot polish: **4,836 VALID**. Verdict: the cards showed that symmetric and exact routes stop
at 8; the gain came from co-designing the hub graph, which the cards' negative results pointed to.

## 2026-10-25 ~15:50–16:40 UTC, cell-10-5 resume (session_01NTgHArireuhKVofyqgzKgX), goal (10,5) > 4,836, round 3

Four cards (research/squads/d10D5/r3/, scoreboard.jsonl), all aimed at 10 freed flags (4,840), from the 1-hole
10-flag states and the valid 9-flag state:
- c1 tabu finisher (all targeted swaps per step, tabu tenure 20-50, restarts): stays at 1; every one of the 424
  swaps covering the hole (freed point 65, target 69) costs >= 5.
- c2 de-crowding (drop the crowded flag 65:202, add uncrowded flags): best 10-flag coverage 4. No graph.
- c3 uncrowded sets from scratch (pairwise opposite points, disjoint lines): coverage 0 only up to k = 6; exact
  matchings are worse than for the crowded orbit set. Negative.
- c4 coverage model + counting: model matches full BFS exactly; counting does not bind (supply ~500 vs 343); the
  binding issue is patchability/crowding (kappa(65) = 3). Predicts 10 only via a joint re-anneal.
Opus during the round: flag moves inside the joint annealing (never accepted: a fresh flag costs ~190), beam repair
with visited-state hashing, reheats, de-crowded and kappa <= 2 flag pairs (worse: 16-27), 10th flags ranked by exact
matching deficiency over all 3,074 candidates (best deficiency 8 vs 20-33 for the earlier ones; joint coverage still
5-7). Verdict: the round added understanding but no record; 4,836 stands. 10 flags needs a better finisher
(compound 2-3 swap ejection chains) or a different symmetric skeleton.

## 2026-10-25 ~19:30–20:10 UTC, cell-10-5 resume 3 (session_01QqmMPMEBdPHeTrrfhst9b1), goal (10,5) > 4,836, round 4

Opus before the round: an exact CP-SAT large-neighbourhood search for the coverage phase (r4/lns.py; the model is
exact, routes with two variable assignments are AND terms). On both 1-hole 10-flag states every neighbourhood tried
(80-160 points, and one 279-point model for 15 minutes) is optimal at 1 hole. Filling the 12-13 unused hub slots of
those states (r4/fillhub.py, 80 hub edges) does not help: the hole targets lie on no freed line.
Eight cards (research/squads/d10D5/r4/, scoreboard.jsonl), all aimed at 10 flags (4,840):
- c1 ejection chains (route counts, last-route losses, 3-level exact lns_step chains): 1.
- c2 other 10th flags on the valid 9-flag state + dmhub: 5 (147:219).
- c3 second family (r2/c3 7 flags + 291:47 + 172:301): 9 flags stall at 5.
- c4 alternating hub-graph rewiring and LNS: 1; hub edges provably cannot cover these holes (targets on no freed line).
- c5 replace the crowded flag 65:202 by another: 9 at best.
- c6 iterated local search (1-3 swap kicks + exact CP-SAT repair, 174 iterations): 1.
- c7 Hungarian (linear assignment) breakout on the whole sigma: 1.
- c8 relaxation analysis: flag 3 (65) alone is satisfiable by 20 single swaps, each breaking >= 9 targets, mostly of
  flag 6 (398, collinear with 65).
Verdict: the round confirmed with eight independent methods that the 1-hole 10-flag states are local dead ends; no
card reached 0. Opus's gain came from a different direction during the round (FLAGDEL, below in cells/d10D5.md).
After the round (Opus): FLAGDEL, i.e. delete a freed flag's own edge and give it 3 hubs per side (+2 per converted
flag; research/squads/cells/d10D5.md). With one converted flag the pipeline reached coverage and D1 0 quickly; the
coset-0 endgame stalled at 2 pairs for every annealer and route-surgery search, and was closed by lns2.py (exact
CP-SAT on sigma with coverage, D1 and all unmixed pairs' routes as constraints, with "best-flip" nu moves):
**4,838, apsp VALID** (research/squads/d10D5/hubs/checks/d10D5_n4838_CHECK.md). The squad did not contribute to this
step directly; its eight negative results are what moved the search off the 10th flag.
