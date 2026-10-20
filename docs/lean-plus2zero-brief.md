# Lean brief: the four hats WITHOUT changing the plane (zero-change +2)

Source: research/plus3/plus3.tex §"The four hats without changing the plane" (Proposition prop:zero) and
research/plus3/construction0.py. Construction: keep PG(2,q) (any projective plane of order q with a frame) completely
intact; add points Q, H_i and lines M, K_i as in the fourth hat, but put the rotation on the copies: H_i also lies on
AX_{s(i)}, K_i also contains X_{s^-1(i)}, Q misses AX_1, AX_2, AX_3, H_a misses AX_a (read the exact incidences from
the .tex and construction0.py). Order 2(q²+q+6), max degree q+2, diameter 3, plane = induced subgraph.

Master already has lean/BipartiteDD/Plus2/ (Plus2.plus2: the rotating version for any `ProjectivePlane P L` with a
`Frame`) and lean/BipartiteDD/Regular/Plus2.lean (regular completion). Reuse the Frame structure and the proof style.
Targets (new folder lean/BipartiteDD/Plus2Zero/; push after each):
1. The incidence structure and graph, `zero_isBipartiteDegDiam : ∃ G : SimpleGraph (Fin (2*(q^2+q+6))), IsBipartiteDegDiam G (q+2) 3`
   for every projective plane of order q ≥ 4 (or the bound the .tex needs) with a frame.
2. The plane's incidence graph is an induced subgraph (state as: the restriction to P ⊕ L equals the plane's graph).
3. Regular version via the existing completion machinery (Regular/Plus2.lean pattern), if the deficient sets match.
Rules: `scripts/stop_check.sh` before each step; builds via `scripts/guarded.sh HOURS ...`; 4-hour limit; push hourly.
No `sorry`/`admit`/`axiom`/`native_decide` in finished files; only propext, Classical.choice, Quot.sound
(Plus2Zero/Axioms.lean + .out.txt). Branch `lean-plus2zero` from origin/master. Report statements, build, axioms.
