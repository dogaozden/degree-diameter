# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 17:50 UTC, exp2-squad (Opus session_01PyvE8WWpo24zEiUSQLSaqN), round 1

Goal: raise (7,7) 23,436, (9,7) 117,648, (11,7) 398,580. Before the round Opus had found the construction
(H(q) × Z3 plus one extra edge per vertex; any matching works; freed pairs with 2 hub vertices each) and had
(7,7) 23,462 (K = 13), (9,7) 117,650 and (11,7) 398,582 (K = 1), all apsp VALID. Cards (folder research/squads/exp2/r1/):
- c1: hub graph = GQ(3,3) incidence graph, K = 40 at q = 5 → unsolved (proxy stalled near 4,600).
- c2: random sparse hub graphs at q = 5, growing K → **K = 18 VALID 23,472** (Opus re-checked: apsp VALID); K = 24 reached cost 31, timed out.
- c3: (9,7) with K = 13 (PG(2,3) hubs, freed points pairwise opposite) → **117,674 VALID** (re-checked); K = 21 (PG(2,4)) unsolved.
- c4: (11,7) with K = 31 (PG(2,5) hubs) → unsolved (proxy 126K after 450 s; far too slow at q = 9).
- c5: search speed: hub-route terms in the proxy → 1.12× faster on K = 13; suggested the two-down routes next.
- c6: super-hubs (second-order vertices on hubs) → base built, no valid graph in the time box.
- c7 (wildcard): per-level bijections M0, M1, M2 → valid but no gain (23,436); a hub needs a neighbour in all 3 levels.
- c8: four copies (Z4) with free voltages → hopeless (~390 uncovered targets per source after local search).
Kept: growing K with random hub graphs (c2), small PG hub graphs at q = 7 (c3), proxy terms for hub routes (c5;
Opus turned it into static hub-graph coverage, 4.5× faster). Opus meanwhile added the type-2 pre-pass (4× faster at
q = 5), best-of-k moves and pair dropping. Next: round 2 (K = 24–32 at q = 5 with drop salvage, conflict geometry,
(9,7) K = 21, (11,7) K = 7, a down-down proxy, a wildcard).
