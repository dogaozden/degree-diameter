# Lean brief: Corollary C1 in full, through W(3,q) directly (no Klein correspondence)

Goal: for every odd prime power q and every even j ≥ 2, a bipartite graph on 2(q²+1)(q+1+j) vertices with maximum
degree q+1+j and diameter 4. Statement, in the Singer setting of lean/BipartiteDD/SingerC (on master):
`theorem corC1 (S : Setting K p) {j : ℕ} (hj : Even j) (hj2 : 2 ≤ j) :
   ∃ H : SimpleGraph (Fin (2 * (S.q ^ 2 + 1) * (S.q + 1 + j))), IsBipartiteDegDiam H (S.q + 1 + j) 4`

## Why no Klein step is needed
The incidence graph of Q(4,q) is the incidence graph of W(3,q) with the sides swapped. So C1 is the copy theorem
`GQST.gqst` applied to W(3,q) itself, with
- point weights w = (j/2) · 1_O, where O = points in Singer classes a or q−a (a 2-ovoid by `SingerC.propC_subspace`:
  every totally isotropic 2-space has exactly 2(q−1) nonzero vectors there, i.e. exactly 2 points). Line weight = j.
- line counts m = j · 1_Σ, where Σ is the regular spread {x·L : x ≠ 0}, L = GF(q²) ⊂ K (these lines are totally
  isotropic, see NOTE.md Section 5.2 "Lines of the regular spread", and every point lies on exactly one). Each point
  is on exactly j line copies.
Vertex count: (q+1)(q²+1) points + (q+1)(q²+1) lines + (j/2)·2(q²+1) + j(q²+1) = 2(q²+1)(q+1+j).

## Autopilot rules (always)
- Before each step, run `scripts/stop_check.sh`. If it prints STOP: commit what you have, push, and end.
- Long commands go through `scripts/guarded.sh HOURS ...`. Total time limit: 4 hours. Push progress every hour
  (finished files must be `sorry`-free; work in progress stays out of the main import chain).
- Build one heavy module at a time.

## Steps (each one is a milestone worth pushing)
1. Branch `lean-c1` from origin/master; `lake exe cache get`. Read SingerC/*.lean (form `S.B`: F-bilinear, alternating,
   nondegenerate — `B_nondeg`, `B_self`, `B_antisymm`), GQST/Defs.lean and GQST/Main.lean.
2. W(3,q) as `GQst P L q q`: P = 1-dimensional F-subspaces of K (or `Projectivization S.F K`), L = 2-dimensional
   totally isotropic F-subspaces, p ∈ l iff p ≤ l. Prove: q+1 points per line; q+1 lines per point (lines through p
   are the 2-spaces of p^⊥ containing p; p^⊥ has dimension 3); `one_line`; `gq_ax` (for p ∉ l, p^⊥ ∩ l is a point,
   because l ⊄ p^⊥ — otherwise ⟨p, l⟩ would be a totally isotropic 3-space, impossible when B is nondegenerate).
3. The 2-ovoid: from `propC_subspace`, every line meets O in exactly 2 points.
4. The spread: x·L is a totally isotropic 2-space for x ≠ 0, and every point lies on exactly one of them.
5. `corC1` from `GQST.gqst` with a = b = j, then compute the vertex count. Also state the j = 2 case:
   n_b(q+3, 4) ≥ 2(q²+1)(q+3).
6. Add `#print axioms` lines to lean/Axioms.lean, regenerate Axioms.out.txt. No `sorry`, `admit`, `axiom`,
   `native_decide`; only propext, Classical.choice, Quot.sound. Commit and push to `lean-c1`.
Report: which steps are done, theorem statements, build result, axioms lines. If you stop before step 5, say exactly
which lemma is left.
