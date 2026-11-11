# STATUS: singer (general existence of `SingerC.Setting`)

## Done

All three main theorems build and are sorry-free. Their axioms are exactly `propext`, `Classical.choice`,
`Quot.sound` (`lean/BipartiteDD/LeanMaxx/Singer/Axioms.out.txt`).

Files (all new, under `lean/BipartiteDD/LeanMaxx/Singer/`):

- `Setting.lean`
  - `galoisFintype`: a `Fintype` instance on `GaloisField p n` (Mathlib gives only `Finite`).
  - `setting p hodd e he`: the `SingerC.Setting` over `GaloisField p (4 * e)`. `card_eq` comes from
    `GaloisField.card`; `g` is `IsCyclic.exists_generator` on the unit group, with `orderOf_g` proved as in
    `SingerC.Regular5440.setting13`.
  - `setting_exists` (**main**): for an odd prime `p` (`[Fact p.Prime]`, `Odd p`) and `e ≥ 1`,
    `∃ S : Setting (GaloisField p (4 * e)) p, S.q = p ^ e`.
- `Corollaries.lean`
  - `transport`: moves an `IsBipartiteDegDiam` witness along equal vertex counts and equal parameters.
  - `corC1_all` (**main**): for every prime power `q` with `Odd q` (`IsPrimePow q`), every even `j ≥ 2`:
    a graph on `Fin (2 * (q ^ 2 + 1) * (q + 1 + j))` with `IsBipartiteDegDiam H (q + 1 + j) 4`.
  - `regular_W3_all` (**main**): for every odd prime power `q`, a `Colorable 2`, `(q + 3)`-regular graph on
    `Fin (2 * (q ^ 2 + 1) * (q + 3))` with `ediam ≤ 4`.
- `Main.lean`: aggregator (imports `Setting` and `Corollaries`).
- `Axioms.lean`: `#print axioms` for the three main theorems; output in `Axioms.out.txt`.

Build: `lake build BipartiteDD.LeanMaxx.Singer.Main` succeeds (Lean 4.34.1, Mathlib `d13f23b7`, with the `SingerC`
chain built from source). Only existing `SingerC` modules emit linter warnings; the new files are warning-free.

Grep: `grep -w -E 'sorry|admit|axiom|native_decide|implemented_by|extern|unsafe'` over the new files finds nothing.
The only substring hit for `axiom` is the `#print axioms` command in `Axioms.lean`.

## Statement choices

- `setting_exists` takes an explicit `p` and `e` rather than an existential over types. The field is the concrete
  `GaloisField p (4 * e)`, so the statement needs no universe or instance-argument quantification.
- `corC1_all` and `regular_W3_all` quantify over `q : ℕ` with `IsPrimePow q` and `Odd q`. Inside the proof,
  `isPrimePow_nat_iff` gives `q = p ^ e` with `p` prime and `e > 0`, and `Nat.odd_pow_iff` gives `Odd p`. So they
  cover exactly the odd prime powers, and the field is hidden inside the existential.
- The two corollaries stay as the card asks: `corC1` for every even `j ≥ 2`, and the regular copy graph with
  degree `q + 3`.

## Not done / out of scope

- `research/theorems/POLISHED.md` §9 still lists "a general existence lemma for `SingerC.Setting`" as not
  formalised (line 83 of the polished branch copy, and §5 "the library constructs them explicitly only for q = 13").
  The new theorem closes that gap. I did not edit the note, since it is an existing file. The coordinator can update
  it, for example to point at `BipartiteDD.LeanMaxx.Singer.setting_exists`.
- `SingerC.Regular5440.setting13` is left as it is. Its data is now a special case of `setting 13 _ 1 _`, but no
  identification lemma is proved.

## Blocked

Nothing.
