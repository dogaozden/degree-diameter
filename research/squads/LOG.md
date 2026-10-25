# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.

## 2026-10-25, thm-smallfamilies resume (Opus, branch claude/thm-smallfamilies-formulas-49l6io), round r3-smallfam

- **Goal:** not a search. Check whether the session's new theory is already known (literature) and whether it is
  right (refereeing): the fibre bound (§2.3 of SMALL_DEGREE_FAMILIES.md), the growth corollary (§2.4) and the (3,7)
  orbit theorem (§2.5).
- **Brief:** `research/squads/r3-smallfam/BRIEF.md`. Scoreboard: `research/squads/r3-smallfam/scoreboard.jsonl`.
- **Run:** 06:15–06:45 UTC, 4 Haiku cards (effort max), light CPU, alongside the main session's screens.

| card | question | answer |
|---|---|---|
| c1 | Is the fibre bound or the growth bound published? | Nothing matching in any readable source. Dougherty–Faber is abelian only. Macbeth–Šiagiová–Širáň (2012): every copy refused access (HTTP 403), so its metacyclic result is unverified. Confidence low |
| c2 | How were (3,10) 800 and (3,7) 168 built; any post-2012 records in the open cells? | The five values are the wiki's as of March 2013 (DS14v2 Table 4). The attributions to Delorme–Gómez–Quisquater and Conder–Nedela come from the wiki colour key and were not confirmed in the survey. No post-2012 bipartite result beating any of the five was found (confidence medium-low; the live wiki returned HTTP 503) |
| c3 | Referee the fibre bound and cyclobound.py | No error in the proof or the code. Verified on 7 groups that φ maps balls onto balls, per side and fibre. Found one real gap: the squarefree-m remark needs the normal-form unit condition (counterexample m = 15, r = 7). Also two code nits and one wording nit |
| c4 | Referee the growth corollary and the (3,7) theorem | No gap in the (3,7) theorem (bases, lift correspondence, orders against the Moore bound, GAP counts). Gaps: §2.4 never stated the Z^(Δ−1) action (0 failures in 2,000 random words once stated); the order-42 2+2 run cited for Conder was not in `runs/` |

- **Kept:** every point raised by c3 and c4 was fixed in the write-up or the code (commit "referee fixes from squad
  r3"). The order-42 run is now saved as `runs/lift_b22_D7_order42.tsv`.
- **Verdict:** a refereeing round is a good use of a squad. Two of four cards found real, fixable problems that the
  main session had missed. None of them changed a result.

## 2026-10-25, thm-smallfamilies resume (Opus, branch claude/thm-smallfamilies-formulas-49l6io), round r2-smallfam

- **Goal:** a cubic bipartite graph beating (3,10) 800, (3,9) 506 or (3,7) 168, by lifts of bases with 6, 8 or
  10 vertices (never searched) and one non-lift wildcard.
- **Brief:** `research/squads/r2-smallfam/BRIEF.md`. Scoreboard: `research/squads/r2-smallfam/scoreboard.jsonl`.
- **Run:** 04:45–05:15 UTC, 8 Haiku cards (effort max), 20-minute boxes. The main session's (4,8) screen shared the
  4 cores. Each subagent's shell is its own scheduling group, so `nice` did not protect the screen: it ran at a
  quarter of its speed while the squad was active.

| card | strategy | best (lower cost is better; all valid = false) |
|---|---|---|
| c1 | (3,10), 3+3 base b33_0, all groups of order 134–145, lanneal screen | cost 10 in the screen; a 60 s re-anneal of C17 : C8 (136,3) reached **cost 2**, the same near miss the voltage-lifts session had searched exhaustively at 816 |
| c2 | (3,10), b33_1 and b33_2 (K3,3), orders 134–138 | **cost 4**, K3,3 over SmallGroup(136,3) = C17 : C8 (816 vertices) |
| c3 | (3,10), 4+4 bases, orders 101–106 (2 of 6 bases done) | cost 24, the cube over C13 × Q8 (104) |
| c4 | (3,9), b33_1, orders 85–95 | cost 36, C11 : C8 (88) |
| c5 | (3,9), 4+4 bases, orders 64–70 | cost 32, the cube over orders 65–70 (all six bases screened) |
| c6 | (3,7), exhaustive: K3,3 at orders 37–42, the cube at 22–26 | none (best costs 60 and 8); found a gap in allgroups.py (below) |
| c7 | (3,7), the 15 5+5 bases, orders 17–25 (226 of 510 pairs) | cost 16, b55_1 over C17 |
| c8 | wildcard: 2-switch annealing of general cubic bipartite graphs at (3,7), 170 vertices | cost 92 (the start: Conder's 168 graph with two vertices spliced in) |

- **Kept and checked by the main session:**
  - c2's lead. K3,3 over C17 : C8 is exhaustively negative: 17,608,192 assignments up to Aut(G), best cost 4
    (`runs/d3D10_k33_sg136_3_exhaustive.txt`, plus the identity pass).
  - c6's bug report was correct. In lift mode, `allgroups.py` left the identity out of the first free voltage's
    plan. That is harmless when the first free edge is parallel to a tree edge, since parallel edges need distinct
    voltages, but wrong for K3,3, the cube, b55_13, b55_14 and the 6+6 bases. Fixed. The earlier K3,3 run at (3,7)
    (orders 29–36) was redone for all of 29–42 (`runs/lift_b33_2_D7_idfix.tsv`): 100 groups, no solution, best cost 6.
    With the Haar and 2+2 results this closes every base with at most 6 vertices at (3,7).
- **Verdict:** no record. The squad added breadth, about 400 (base, group) pairs that are all negative, and one
  real bug fix. CPU sharing was the limit, not ideas.

## 2026-10-24, thm-smallfamilies (Opus, branch claude/small-degree-families-g7zllq), round r1-smallfam

- **Goal:** beat (4,8) 2,184 or (4,9) 4,970, after (4,7) had just fallen to Haar graphs of order-432 groups
  (Heis(F_9) ⋊ C16 and two others).
- **Brief:** `research/squads/r1-smallfam/BRIEF.md`. Scoreboard: `research/squads/r1-smallfam/scoreboard.jsonl`.
- **Run:** 18:41–19:20 UTC, 8 Haiku cards (effort max). The machine ran at load 5–13 on 4 cores, so most cards
  overran the 15-minute box.

| card | strategy | best (lower cost is better; all valid = false) |
|---|---|---|
| c1 | Heis 3^{1+2} ⋊ H (× C_n), (4,8), exhaustive | cost 20, SmallGroup(1296,2900) |
| c2 | Heis 5^{1+2} / 7^{1+2} ⋊ H, exhaustive | cost 22, 5^{1+2} ⋊ C12 (1500) at (4,8); (4,9) unrun |
| c3 | affine F_q^n ⋊ H, exhaustive | cost 14, Aff(2,5,C24:C2) (1200) at (4,8); ASL(2,5) at (4,9): 25 uncovered |
| c4 | PSL/PGL/SL × C_n, haar_gen3 annealing, (4,8) | cost 9, PSL(2,7) × Z7 (1176) |
| c5 | SmallGroups 1093–1139 with small G/G′, exhaustive | cost 331; dihedral-type groups, a poor filter |
| c6 | composite-m metacyclic, exhaustive | cost 6, Z77 ⋊ Z15 = (C11:C5) × (C7:C3) (1155) |
| c7 | (4,9) annealing on groups with tiny abelianization | cost 8, PSL(2,8) × Z5 (2520, 90 s) |
| c8 | wildcard: Z_547 lifts of the Δ=4 2+2 bases | cost 894 |

- **Kept:**
  - PSL(2,8) × Z5 at (4,9) and PSL(2,7) × Z7 at (4,8) get longer anneals in the main session
    (`research/theorems/smallfam/runs/followup_r1.txt`).
  - c6's composite-m idea became the record-shaped scan of Z_pq ⋊ Z_k groups with a central involution, the shape of
    Loz's (4,8) group (1092,4) = (C7:C3) × Dic13, which the main session identified meanwhile.
- **Verdict:** no record. The squad added breadth: about 60 more groups across 7 families, cleanly negative.
  c5 also flagged a missing SmallGroups data package, which the main session had found and installed
  (gap-smallgrp-extra).
