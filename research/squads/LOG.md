# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-29 13:00 UTC, job "thm-conics" (branch claude/d7-cells-theorems-7h6iex), round d7thm-r1

Goal: independent checks of the statements of research/synthetic/D7_THEOREMS.md (not a search). Six Haiku cards, own
code each (brief: research/squads/d7thm-r1/BRIEF.md; scoreboard there).
- c1: H(q) built from the quadric for q = 3, 5, 7; spread, whiskers, nu, S_0, R_L, R_H, elliptic section. 21/21 pass.
- c2: q = 9, 11 (hexgen2 + own GF(9)), every admissible c. 72/72 pass; negative control (c with -c a square) fails.
- c3: even q = 2, 4, 8 (H(4) own, H(8) hexgen2), every zero-free (c0, c1); q = 2 has no zero-free G. 75/75 pass.
- c4: end-to-end typed layouts (alternating, k = 2, 3) without hubs at q = 3, 4, 5: diameter 7 (apsp_mt), slot minima as
  predicted, controls (one extra freed element) diameter 8; q = 5 with 7+7 hubs and a Fano hub graph: diameter 7. 106/106.
- c5: hub-graph lemmas (blow-up, sums, pendant trees with separate colour sizes): 70/70; control (tree part not last)
  fails as expected.
- c6: slot-count theorem: all regular tournaments on <= 7 levels, 200,000 random on 9 and 11; closed forms to k = 40.
  Found that the closed form for odd k needs the hypothesis Lam - m >= floor(k/2)(P - Lam) (only fails for k far
  above q); the hypothesis is now stated in Section 2.
Kept: all of it as the computer checks of Sections 1-4. Opus re-ran c4 at q = 4 with a fresh seed (same results).
The squad added independent confirmation and one correction (c6); no new idea was asked for.
