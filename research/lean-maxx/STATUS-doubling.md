# Lean-maxx job "leanmaxx-doubling": Theorem 1.2(d) — STATUS

Card: "doubling". Target: Theorem 1.2(d) of `research/theorems/POLISHED.md` §1 (branch `claude/thm-polish-2oddll`),
which §9 lists as not formalised. Branch: `claude/leanmaxx-doubling-ujetvc`.

## Done

Theorem 1.2(d) is formalised, with no sorry, admit, native_decide, or extra axioms.

- **Main theorem:** `BipartiteDD.LeanMaxx.Doubling.part_d` (file `lean/BipartiteDD/LeanMaxx/Doubling/PartD.lean`).
  - Hypotheses: `hm : 2 ≤ m` (the note's m ≥ 2) and `hD : (levelled G m h).ediam ≤ D`.
  - Conclusion, for all `x y : V` with `x ∈ {v | 0 < h v}` and `y ∈ {v | 0 < h v}` (x = y allowed):
    `∃ z, z ∉ {v | 0 < h v} ∧ G.edist x z + G.edist z y ≤ D`.
  - This is the note's "the conclusion of (C_D) holds for every pair x, y ∈ A₀". It needs no reachability hypothesis.
- **Corollary:** `BipartiteDD.LeanMaxx.Doubling.part_d_condC`: `CondC G {v | 0 < h v} D` (the existing `CondC`
  from `Doubling/Core.lean`), obtained from `part_d` by dropping the reachability hypothesis.
- Reused: `levelled`, `Ver`, `Agree`, `levelled_adj`, `proj`, `CondC`, `edist_le_of_hom`, `exists_walk_of_edist_ne_top`.
- Helpers in the same file: `constVer`, `firstLetter`, `firstLetter_constVer`, `firstLetter_eq_of_adj`,
  `firstLetter_eq_of_walk`.

### Is 1.2(d) a citation or a proof?

The note proves it. The paragraph "(d) Conversely, if S^(m)_A has diameter at most D …" in the proof of Theorem 1.2
gives an argument. Only the statement is attributed to Delorme, so I formalised the note's proof rather than a citation.

### Statement choices

- **Graphs, not incidence structures.** As for (a)–(c), the Lean statement is for a graph `G` with the levelled
  doubling `levelled G m h`, where `A_i = {v | i < h v}`. For an incidence structure S, the incidence graph of
  `S^(m)_A` is `levelled Γ(S) m h`, since versions are adjacent iff the elements are incident and the words are
  comparable. So the graph statement gives (d) for incidence structures.
- **Fewer hypotheses than the note.** The note's (d) is stated under "S has diameter at most D ≥ 2". The proof uses only
  the doubled diameter and `m ≥ 2`, so the Lean hypotheses are `hm` and `hD` alone. This is a weaker hypothesis set
  and a stronger theorem. No hypothesis was weakened.
- **No (L0), (L1), or (C_D) hypothesis.** The note's (d) does not use them.

### Build and checks

- Toolchain: Lean v4.34.1 via elan, Mathlib from `lake exe cache get` (rev d13f23b7).
- `lake build BipartiteDD.LeanMaxx.Doubling.PartD`: builds cleanly, no warnings after cleanup.
- `lean/BipartiteDD/LeanMaxx/Doubling/Axioms.lean` prints the axioms of `part_d` and `part_d_condC`; output is in
  `lean/BipartiteDD/LeanMaxx/Doubling/Axioms.out.txt`. Both show exactly `[propext, Classical.choice, Quot.sound]`.
- grep for `sorry|admit|axiom|native_decide|implemented_by|extern|unsafe`: no hits in `PartD.lean`. The only hits in
  `Axioms.lean` are the two `#print axioms` lines themselves.

### Files added (all new, nothing existing edited)

- `lean/BipartiteDD/LeanMaxx/Doubling/PartD.lean`
- `lean/BipartiteDD/LeanMaxx/Doubling/Axioms.lean`
- `lean/BipartiteDD/LeanMaxx/Doubling/Axioms.out.txt`
- `research/lean-maxx/STATUS-doubling.md` (this file)

## Partial

None. All of the card's Theorem 1.2(d) is done.

## Remaining (outside this card)

- The "equality only if" clause of Theorem 1.2(b) (degree `deg x^w = deg x + m − 1` only if `x` is incident with an
  element of level `λ(x)+1`) is still not formalised. The existing `levelled_degree` gives only the bound `Δ + (m − 1)`.
- `POLISHED.md` §9 still says "Theorem 1.2(d) is not formalised". It lives on branch `claude/thm-polish-2oddll`, which
  this job does not touch, so that line is unchanged. It needs updating once this lands.

## Blocked

Nothing.
