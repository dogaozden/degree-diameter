# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 ~17:47–18:17 UTC, thm-buildings (Opus, session_013HBUN7xkpWbWCiMo7oMNJK), round buildings-r1-lit

Goal: decide whether "lim n_b(Δ,D)/M_b(Δ,D) = 1" (bipartite degree–diameter, D ∉ {2,3,4,6}) and the diameter of
flag graphs of higher-rank buildings are already in the literature. Literature round (no numeric scorer): score
3 = explicit statement found, 2 = strong related statements, 1 = partial, 0 = nothing. 8 Haiku cards, effort max.

Cards (best score):
- c1 Delorme, J. Graph Theory 1985 (bipartite paper): abstract only gives lim inf n_b Δ^(1−D) > 0 (1).
- c2 Delorme, Eur. J. Combin. 1985, and D = 7: found BŠŠ 2017, "lim sup = 1 only for k ∈ {2,3,5}, k = 7 ≥ 1.57⁻⁷";
  noticed the octagon quotient (1).
- c3 Miller–Širáň DS14v2: p. 36, bipartite lim inf = 1 known only for D = 2,3,4,6; p. 19 general (2).
- c4 citations of CvB–K and Isham et al. after Aug 2026: none states the bipartite version. Its claim that CvB–K
  state it was a misreading of the edge version; I checked (2).
- c5 references: Fomin–Zelevinsky Lemma 2.1 for (C1); no source for the general diameter statement (1).
- c6 pre-2026 bipartite constants: DS14 and the Delorme abstract; no constant equal to 1 beyond D = 2,3,4,6 (2).
- c7 polygons, octagons, Benson: no octagon construction anywhere (Bachratý 2021); Comellas's Delorme products (2).
- c8 wildcard: live wiki and Comellas tables; nothing from buildings (2).

Kept: DS14 p. 36 and p. 19 quotes (c3, c6), FZ Lemma 2.1 (c5, verified myself), BŠŠ 2017 (c2), Bachratý 2021 (c7),
the general-table values (c8, cross-checked against the saved Wikipedia table). No card found a source for the
two questions, which is itself the answer: neither is in print. One false claim was caught (c4).

Next: wrote research/theorems/BUILDINGS.md. No second squad. The remaining questions were proofs (done by me) and
finite comparisons (done by script). A computational squad on "building-derived graphs beating table cells" had
nothing to aim at: table_cells.py shows that every candidate is below our values. Did the squad help? Yes, for
breadth and speed: 8 directions in 12–29 minutes of wall time, and it surfaced BŠŠ 2017 and Bachratý 2021, which I would not have
looked for. It found nothing that changed the conclusion I had reached from the two 2026 papers.
