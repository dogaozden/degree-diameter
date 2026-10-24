# STATUS lift58410: Δ5·D8 on 9,576 and Δ4·D10 on 12,246

**Status: done.** Both record theorems build, and their axioms are only `propext`, `Classical.choice`, `Quot.sound`.

    theorem nb_5_8_9576 : ∃ H : SimpleGraph (Fin 9576), BipartiteDD.IsBipartiteDegDiam H 5 8
    theorem nb_4_10_12246 : ∃ H : SimpleGraph (Fin 12246), BipartiteDD.IsBipartiteDegDiam H 4 10

Axioms: `lean/BipartiteDD/Haar/LiftA/Axioms.lean` and `Axioms.out.txt` (`lake env lean` output, both lines show the
three standard axioms). No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `extern` in the new files.
Certificates are checked by `decide +kernel`.

## The graphs (confirmed first)
- Coordinator check rebuilt: `python3 build.py meta 266 18 17 0,0 51,5 129,13 156,5 110,11` and
  `python3 build.py meta 157 39 9 0,0 151,25 63,2 38,5`, then `apsp` (compiled from `apsp.c`) on both.
  Results: `n=9576 degree 5 bipartite diameter=8 RESULT VALID`, and `n=12246 degree 4 bipartite diameter=10
  RESULT VALID`. The build and check were run in the scratchpad, not in the repo.
- Group checks in the generator: `r^k ≡ 1 mod m` for both groups.

## Covering facts (Python, exact word shapes of the Lean lemmas)
- Δ5·D8, `G = Z_266 ⋊_17 Z_18`, `|G| = 4788`, `S` of 5 elements:
  - `hA` (4 pairs `a⁻¹ b`): covers all 4788 elements.
  - `hB` (4 pairs `a b⁻¹`): covers all 4788.
  - `hAB` (3 pairs `a b⁻¹` then `s`): covers all 4788.
- Δ4·D10, `G = Z_157 ⋊_9 Z_39`, `|G| = 6123`, `S` of 4 elements: the nine-letter cover
  `x₁ x₂⁻¹ x₃ x₄⁻¹ … x₈⁻¹ x₉` covers all 6123 elements. (A first probe used zero steps and gave a wrong count of 1;
  that was my script's bug, not a property of the group.)

## Modules (all under `lean/BipartiteDD/Haar/LiftA/`, new namespace `BipartiteDD.Haar.LiftA`)
- `Meta266.lean`, `Meta157.lean`: the metacyclic groups (same construction as `Haar/D6D7/Group.lean`), with
  `equivG : Grp ≃ Fin 4788` and `Fin 6123`.
- `D5D8/Check.lean`, `D5D8/StageA00–A11`, `StageB00–B11`, `StageC00–C11`: 12 stages of 399 codes per cover, 19 bits per
  code (base 5, 8 digits; 7 digits for `C`). `D5D8/Cover.lean`: `coverA`, `coverB`, `coverC`.
- `D5D8/Record.lean`: `equiv9576`, the comap graph, and `nb_5_8_9576`. It uses `isBipartiteDegDiam8_of` from
  `Haar/Diam8.lean` (not the `D7D8` wrapper).
- `D4D10/Check.lean`, `D4D10/StageD00–D12`: 13 stages of 471 codes, 18 bits per code (base 4, 9 digits).
  `D4D10/Cover.lean`: `coverD`, in the right-nested form of `Haar/Diam10.lean`.
- `D4D10/Record.lean`: `equiv12246`, the comap graph, and `nb_4_10_12246`, via
  `haar_isBipartiteDegDiam10_of_equiv`.
- `Axioms.lean`, `Axioms.out.txt`.
- Generator: `research/lean-haarD/gen_lift58410.py`. It writes all the above from the two sol files, and its
  word checks are re-done by direct multiplication before any Lean file is written.

## Build log (one module per `lake build`, sequential)
- `lake exe cache get` worked (`cache.mathlib.org`), so Mathlib came from the cache.
- Meta266, Meta157, D5D8.Check: ~3 s each. One D5D8 stage: ~6 s. All 36 D5D8 stages, then Cover, Diam8, Record: pass.
- D4D10.Check, all 13 stages (~95 s total), Cover, Diam10, Record: pass.
- Every module of both records builds; no module timed out or hit a heartbeat or recursion limit.
- One fix on the way: the graph defs `G9576` and `G12246` need `noncomputable` (their equiv is noncomputable).

## Notes and deviations
- Branch: the session designated `claude/lift58410-haar-lean-v7xd6m`, so the work is on that branch rather than
  `lean-haarD-lift58410`.
- I did not append these theorems to the merged `lean/Axioms.lean` or regenerate its `Axioms.out.txt`. That
  file imports every record module, so regenerating it means building all of them. The job's own
  `Axioms.lean` / `Axioms.out.txt` in `LiftA/` covers both records.
- Network: a direct probe of `cache.leanprover-community.org` was refused by the proxy policy, yet `lake exe cache get`
  downloaded all 8,908 Mathlib files from `cache.mathlib.org`, so no workaround was needed.
