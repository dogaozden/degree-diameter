# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 04:47–05:45 UTC, hexagon-family (Opus lead, cloud session), round hexfam_r1
Goal: larger freed sets for the D = 7 hexagon records: partial ovoids of Q(6,q) (q = 5, 7, 8, 11, 13; best 72, 288,
217, 756, 792) and non-collinear sets of H(9) (best 4,291). Scorer: research/projects/hexagon-family/tools/povcheck.
Cards (one line each) and best score:
- c1 PSL(2,q) on binary sextics, orbit unions + max-weight clique: q7 288 (tie), q11 336, q13 196.
- c2 J1 < G2(11) and 2^3.L3(2) on octonions, orbit cliques: q11 756 (tie, a different 756 set), q13 504 (no full report).
- c3 cyclic tori of order q^3+1 and q^3-1, orbit cliques: q5 72 (tie), q7 288 (tie), q11 148.
- c4 W(E7) reflection subgroups and monomial groups: q5 ≤ 60 so far (no report at log time).
- c5 ARW-style swap search from the best sets: no gain at any q; every outside point of the q = 11 set is orthogonal
  to 60–78 of its points (no 1-, 2-, 3-tight points), so swaps cannot work there.
- c6 ARW iterated local search on the collinearity graph of H(9) from the 4,291 set: **4,306** (new).
- c7 q = 8: Sp(6,8) torus of order 513 orbits (≤ 76) and ILS from 217: no gain.
- c8 wildcard, affine chart opposite e4 with random cyclic similitude groups: q11 262; proved that 2-dim
  anisotropic translation subgroups cannot be combined.
Kept: c6's 4,306 → (11,7) 407,192 (all-pairs VALID here). Separately (Opus): a Haar graph of PSL(2,11)×Z13 (Δ = 7,
D = 7, 8,580 per side) as the (12,7) hub graph → (12,7) 681,460 (all-pairs VALID here). Next: long ARW runs at q = 9
(Opus), round 2 with structured groups (G2 root elements now in tools/g2gens.py) and stabilizer-subgroup orbit search.
