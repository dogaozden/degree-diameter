# Lean brief: Theorem D and Theorem R for EVEN q (characteristic 2)

Master has the odd-q development: lean/BipartiteDD/Hexagon/ (H(q) via the split octonions; `[NeZero (2 : F)]`),
lean/BipartiteDD/HexagonD/ (Hermitian spread in Π: x0 + c x4 = 0, Delorme levels, whiskers, theorem4 = exact whiskers,
theoremD), HexagonD/Identity/ (J_z, key identity), HexagonD/Regular/ (theoremR). The even-q mathematics is in
research/evenq/evenq.tex (+ proof_char2.py, proof_J.py, proof_J2.py): in characteristic 2 the quadric has a nucleus, so
use Π_z: X3 = X0 + δX4 + αX2 + βX5 with Tr(δ) = 1; ν(X) = (X2X3 + X2X4 + X4X5)/(δX2² + X2X5 + X5²);
G(a,b) = (c0a + c1b)(a² + ab + δb²) + b³; J_z with J² + J + δ = 0, Q(Jx) = δQ(x), B(x,Jx) = Q(x); closed form
Φ_p = (p2p3 + p2p4 + p4p5 + βp2²)/(δp2² + p2p5 + p5²). Good (c0,c1) exist iff q ≥ 4.

Targets (new folder lean/BipartiteDD/HexagonEven/, reuse as much as possible; push after each):
1. H(q) is a generalized hexagon for every finite field (drop NeZero 2 where possible, or prove the char-2 case
   separately; the status note docs/lean-hexagon-status.md says odd characteristic is used only for dim π_x ≤ 3).
2. The char-2 Hermitian spread (Π with Tr(δ) = 1), Delorme's levels, whiskers — mirror HexagonD.
3. The char-2 J_z and key identity (polynomial identities over a field of characteristic 2: `ring` with
   `CharTwo` lemmas), exact whiskers for q ≥ 4, theoremD_even, and theoremR_even via Regular.regular_of_twin_classes.
Rules: `scripts/stop_check.sh` before each step; builds via `scripts/guarded.sh HOURS ...`, heavy modules one at a time;
5-hour limit; push hourly with a status note. No `sorry`/`admit`/`axiom`/`native_decide`; only propext,
Classical.choice, Quot.sound (Axioms.lean + .out.txt). Branch `lean-evenq` from origin/master.
