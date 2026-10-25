# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 ~16:30 UTC, job d7-family (claude/d7-family-hexagon-mrr6hp), round d7fam-r1

Goal: raise D = 7 records with tonight's hexagon constructions. Cards (research/squads/d7fam-r1/CARDS.md):
- c1 H(11) mirrored set > 768 (annealer with --cmax 62..70, T 0.15/0.3): 768, no gain.
- c2 H(13) mirrored set > 813 (deficit-allowing annealing, cmax 60, lean memory copy mirror_sa5c.py): 813, no gain
  (from scratch plateaus at 808).
- c3 H(5) mirrored set > 81 (exact candidate enumeration + search): 81, no gain.
- c4 H(7) mirrored set > 295 ("drop to gain" annealing): 295, no gain (from scratch 293).
- c5 H(8) mirrored set > 229 (mirror_sa6, full line pool 36,936, --m 16 --sample 400, T 0.1): **230** (k = 13).
- c6 non-concurrent lines of H(11) > 8,246 ((2,3)-swap tabu, ls23.c): 8,246, no gain.
- c7 non-collinear points of H(13) > 14,762 (pack.c and a cluster-kick variant pack2.c): 14,762, no gain.
- c8 wildcard, non-concurrent lines of H(13) > 14,823 (min-degree greedy, spread seeding): 12,816, no gain.
Kept: c5's state; Opus built it (multi.c), checked it with apsp_mt (all pairs, VALID) and recorded (10,7) 225,154
(+2). Next: round 2 applies c5's recipe (full pool, many proposals, low temperature) to q = 5, 7, 11, 13 and continues
q = 8. The plain-set cards (c6–c8) confirm that master's symmetric sets are hard to beat without relaxation; Opus's own
1-defective runs (dpack) show the masks, not the search, limit the relaxed sets on five levels.
