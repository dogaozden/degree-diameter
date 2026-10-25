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
