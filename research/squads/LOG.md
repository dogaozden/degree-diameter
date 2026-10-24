# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


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
