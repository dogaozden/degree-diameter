# leanmaxx-verify: independent check of the six Lean-maxx cards

Verifier: Sonnet session, branch `claude/leanmaxx-verify-9ummw2`, 2026-10-28. I rebuilt everything myself and did not
use any worker's log or `Axioms.out.txt` as evidence. I did not change any proof.

**Result: all six cards pass.** Every module builds, every regenerated Axioms file is identical to the committed one and
shows only `[propext, Classical.choice, Quot.sound]`, the forbidden-token grep is empty, and every main statement says
what its card asks. Details and the few remarks (none a weakening) are below.

## Setup

- Branch made from `origin/master` (ab2f6fb). Merged, in this order, with `git merge --no-edit`:
  `leanmaxx-moore-bound-pv3a5x`, `leanmaxx-projection-r0kehl`, `leanmaxx-singer-setting-exists-bnzyai`,
  `leanmaxx-haarconv-ml9mpb`, `haarbound-moore-bound-qvdupi`, `leanmaxx-doubling-ujetvc`.
  **No conflicts.** `git diff --name-status origin/master HEAD` shows only additions (32 files: 20 `.lean` under
  `lean/BipartiteDD/LeanMaxx/<Card>/`, 6 `Axioms.out.txt`, 6 `research/lean-maxx/STATUS-*.md`). `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain` and `BipartiteDD.lean` are untouched.
- Toolchain: elan 4.2.4 installed fresh in this sandbox; `leanprover/lean4:v4.34.1`, Lake 5.0.0; Mathlib from
  `lake-manifest.json`. `lake exe cache get`: 8908 files downloaded and decompressed (1m41s).
- Machine: 4 cores, 15 GB. No OOM occurred; every build was run alone, in the foreground, one module per
  `lake build BipartiteDD.LeanMaxx.<Card>.<Module>`. Logs are in `/tmp/build_<Card>_<Module>.log` (sandbox only).

## Per card

Build column: every one of the 20 modules returned exit 0 and "Build completed successfully". Imports not yet built
(for example `BipartiteDD.SingerC.Regular5440`, `BipartiteDD.Haar.GraphD`, `BipartiteDD.Doubling.Levels`) were built
as dependencies by the same command. Axioms column: `lake env lean BipartiteDD/LeanMaxx/<Card>/Axioms.lean >
/tmp/<Card>.axioms 2>&1` from `lean/`, then `diff` against the committed `Axioms.out.txt`.

| Card | Modules built (all pass) | Axioms regenerated | Grep (step 4) | Statement fidelity |
|---|---|---|---|---|
| Moore | Layers, Main, Axioms | identical; 2 theorems, 3 std axioms | clean | faithful |
| Projection | Walk, Main, Axioms | identical; 4 theorems | clean | faithful (slightly more general) |
| Singer | Setting, Corollaries, Main, Axioms | identical; 3 theorems | clean; one benign instance | faithful |
| Haarconv | Ball, Converse, Axioms | identical; 4 theorems | clean | faithful |
| Haarbound | Sphere, Arith, Main, Abelian, Axioms | identical; 5 theorems | clean | faithful (both parts) |
| Doubling | PartD, Axioms | identical; 2 theorems | clean | faithful |

Build warnings only: unused variable `hd` (Moore/Main.lean:19), unused simp arguments and deprecated `if_pos`/`if_neg`
(Haarbound/Abelian.lean:88–178), unused variable linter notes. Nothing mentions `sorry`; `grep sorry /tmp/build_*.log`
is empty. The other warnings in the logs come from older modules on master (GQST, SingerC).

### Grep (step 4)

Run over all 20 new `.lean` files:
`grep -nE '\bsorry\b|\badmit\b|^\s*axiom |native_decide|implemented_by|extern|unsafe|ofReduceBool'` returns nothing.
Also searched for `opaque`, `macro`, `syntax`, `elab`, `notation`, `set_option`, `attribute`, `initialize`,
`import Lean`, `run_cmd`, `sorryAx`: nothing. `instance` occurs once:

- `Singer/Setting.lean:18`, `noncomputable instance galoisFintype (n) : Fintype (GaloisField p n) := Fintype.ofFinite _`.
  Mathlib gives `GaloisField` only a `Finite` instance; `Fintype` is a subsingleton and this one is built from that
  `Finite`, so it supplies no false fact and cannot change a statement. The `Fact p.Prime` instances in
  `Singer/Corollaries.lean` are `have`s from the genuine `hp : p.Prime` that `isPrimePow_nat_iff` returns, not global.
- `open scoped Classical` appears in Moore, Doubling (three files); no statement depends on a decidability instance.
- `decide` appears only on closed `Bool`/`Fin 2` facts.

New `def`s are all auxiliary (`constVer`, `firstLetter`, `edgeLetter`, `vq`, `sgn`, `Phi`, `bnd`, `parSum`,
`farVertex`, `sphere`, `LBall`, `RBall`, `layer`, `newCount`, `setting`); none redefines `haarGraph`,
`IsBipartiteDegDiam`, `levelled` or `SingerC.Setting`. The main statements use the repo's own definitions.

### Statement fidelity (step 5)

I printed each main theorem with `#check` (elaborated form) and read it against the card.

- **Moore.** `card_le_moore : ∀ {V} [Fintype V] (G : SimpleGraph V) {d D}, 2 ≤ d → 1 ≤ D → IsBipartiteDegDiam G d D →
  Fintype.card V ≤ 2 * ∑ j ∈ range D, (d-1)^j`. This is the card word for word, with `IsBipartiteDegDiam` as defined in
  `Basic.lean` (2-colourable, `ncard` of every neighbour set ≤ d, `ediam ≤ D`). `card_le_moore_of_regular` is the
  regular case. No weakening.
- **Projection.** `edist_ge`: under h1 (copy edges stay in one copy and project to `B`-edges), h2 (a new vertex is adjacent
  only to copy vertices with its own label), h3 (no new–new edges), for `c x = none`, `x` with no neighbour in copy `j`
  and `c v = some j`: `(B.dist (f x) (f v) + 3 : ℕ∞) ≤ G.edist x v`. This is Theorem 1 of `d12D8_table.md` in general
  form: B need not be bipartite, D₁ need not be even or the diameter (those only matter when one then reads off
  "diameter ≥ D₁+3", which `ediam_ge` does for `B.edist t s = D₁`). `dist_ge` and `walk_ge` are the distance and walk
  forms. `B.dist` is junk (0) if `f x`, `f v` are disconnected in `B`, which only weakens the statement in a case where
  the proof of the table's use never applies; `ediam_ge` rules it out by taking `B.edist t s = D₁`. No weakening of
  substance. I did not check that h1–h3 are satisfiable by the ΩH_q graphs (that is a modelling question, not part of this
  statement).
- **Singer.** `setting_exists p [Fact p.Prime] (hodd : Odd p) (e) (1 ≤ e) : ∃ S : Setting (GaloisField p (4e)) p, S.q = p^e`;
  `corC1_all {q} (IsPrimePow q) (Odd q) {j} (Even j) (2 ≤ j) : ∃ H : SimpleGraph (Fin (2(q²+1)(q+1+j))), IsBipartiteDegDiam H (q+1+j) 4`;
  `regular_W3_all {q} (IsPrimePow q) (Odd q) : ∃ H : SimpleGraph (Fin (2(q²+1)(q+3))), H.Colorable 2 ∧ (∀ v, ncard (N v) = q+3) ∧ H.ediam ≤ 4`.
  Every odd prime power is covered (`Odd q` plus `IsPrimePow q` forces `p` odd and `e ≥ 1`). The vertex counts and
  parameters are exactly those of `SingerC.Setting.corC1` and `regular_W3`, transported by `finCongr`/`regular_comap`
  from `S.q = p^e`. The `Setting` is built from `IsCyclic` of the unit group of `GaloisField p (4e)` (card `(p^e)^4`) with
  a chosen generator; all four fields of the structure are proved, none assumed. No weakening. (The result depends on
  the master modules `SingerC.*`, `GQST.Regular`, which were rebuilt here and carry only the standard axioms through
  `#print axioms`.)
- **Haarconv.** `cover_of_ediam_le_odd (n) : ediam ≤ 2n+1 → (∀ x, IsLeftWord S n x) ∧ (∀ x, IsRightWord S n x)` (the two
  hypotheses of `haar_ediam_le_odd`, without its `S.Nonempty`, which makes the converse stronger);
  `cover_of_ediam_le_even (n) : ediam ≤ 2n+2 → ∀ x, ∃ s ∈ S, IsLeftWord S n (s⁻¹ * x)` (exactly `haar_ediam_le_even`'s `hA`);
  `cover_of_ediam_le_five S (hS : S.Nonempty) : ediam ≤ 5 → (∀ g, ∃ a b c d ∈ S, g = a⁻¹ b c⁻¹ d) ∧ (∀ g, ∃ a b c d ∈ S, g = a b⁻¹ c d⁻¹)`
  (exactly `haar_ediam_le_five`'s `hA`, `hB`; `hS` is kept as in the original though it is implied). I compared these with
  `Haar/GraphD.lean:119,159` and `Haar/Main.lean:164`. `ediam_le_five_iff` combines both directions. No weakening.
- **Haarbound.** `card_le [Fintype G] (S) (S.card = Δ) (2 ≤ Δ) (ediam ≤ D) : Fintype.card G ≤ ∑ j ∈ range D, (Δ-1)^j`, and
  `abelianization_card_le (S) (S.card = Δ) (ediam ≤ D) : Nat.card (Abelianization G) ≤ Nat.card {c : Fin Δ → ℤ // ∑ c = (if D % 2 = 0 then 1 else 0) ∧ ∑ |c i| ≤ D - 1}`.
  Both match; the latter is Theorem 4.3's first inequality `|G/G'| ≤ A(Δ,D)` with ε = 1 for D even, 0 for D odd, as defined
  in §4.2 of `HAAR_D8_10.md`, with no side conditions (the note assumes Δ ≥ 1, D ≥ 2; the Lean statement needs neither).
  The second half of Theorem 4.3 ("hence |G| ≤ |G'|·A(Δ,D)") is not stated in Lean; the card names only the abelianization bound.
- **Doubling.** `part_d (2 ≤ m) ((levelled G m h).ediam ≤ D) : ∀ x y ∈ {v | 0 < h v}, ∃ z ∉ {v | 0 < h v}, G.edist x z + G.edist z y ≤ D`
  is Theorem 1.2(d): the conclusion of (C_D) for every pair of `A₀`, with `A₀ = {0 < h}` and `levelled` the repo's
  Definition 1.1 (versions are `x` plus a string of length `h x`, adjacency = adjacent in `G` and prefix-comparable). It
  does not need `S` to have diameter ≤ D or `D ≥ 2`, so it is slightly stronger. `part_d_condC` is the `CondC G A₀ D` form.
  The statement is for graphs (the incidence graph), as the file says; the incidence-structure form is the same statement.

## Notes

- I treated the committed `Axioms.out.txt` files as untrusted claims; all six equal my regenerated output byte for byte.
- A tool-level `#print axioms` covers the transitive closure, so master modules used (Haar, SingerC, GQST, Doubling) are
  included in what was checked for these theorems, but I did not otherwise audit master.
- I did not check non-vacuity of any hypothesis beyond reading it (for example I did not instantiate Projection's h1–h3).
- `research/lean-maxx/STATUS-*.md` from the workers were not used as evidence.
