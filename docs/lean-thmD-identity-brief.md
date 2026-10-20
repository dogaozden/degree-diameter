# Lean brief: Theorem D, the algebraic core (complex structure J_z and the key identity) — parallel to lean-thmD

Work from branch origin/lean-thmD (it has lean/BipartiteDD/Hexagon/ and HexagonD/Pi.lean, Spread.lean). Do NOT edit
those files; add new files in lean/BipartiteDD/HexagonD/Identity/ only (another job is editing HexagonD/ in parallel).
Source: research/geometry/geometry.tex Lemma 6.6 (complex structure J_z) and Lemma 6.7 (key identity), with the
explicit formulas (J_z, the Tits-residual vector Q(x)·(1,0,0,−c,α,−β), X(z) = γp − J_z p, N, D, ν = N/D, closed form
Φ_p(z) = (p2p3 − p4p5 + βp2²)/(cp2² + p5²)); research/geometry/PROOFREAD.md has the argument. Odd characteristic.
Targets (push after each):
1. Polynomial identities over a commutative ring / field: J_z² = −c, Q(J_z x) = c·Q(x), B(x, J_z x) = 0, the six Tits
   differences of (x, J_z x) = Q|Π_z(x)·(1,0,0,−c,α,−β). These are `ring`/`linear_combination` proofs.
2. For x a singular point in Π_z: ⟨x, J_z x⟩ is a line of H(q) in Π_z (use the Hexagon definitions IsHPair/HLine).
3. N(J x) = c N(x), D(J x) = c D(x) and the polar identities; hence ν is constant on each S-line (z = 0).
4. The key identity: with the constraints φ0(p) = 1, αp2 + βp5 = −1, ν(X(z)) + β³/(α²+cβ²) = Φ_p(z), and its
   increment along (p5, −p2) is −p2³/(cp2² + p5²).
Rules: `scripts/stop_check.sh` before each step; builds via `scripts/guarded.sh HOURS ...`; 4-hour limit; push hourly.
No `sorry`/`admit`/`axiom`/`native_decide`; only the three standard axioms (Identity/Axioms.lean + .out.txt). Branch
`lean-thmD-identity` from origin/lean-thmD. Report statements, build, axioms.
