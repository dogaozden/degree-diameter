# STATUS d4D10b: Δ4·D10 on 12,416 vertices

**Status: done.** The record theorem builds, and its axioms are only `propext`, `Classical.choice`, `Quot.sound`.

    theorem nb_4_10_12416 : ∃ H : SimpleGraph (Fin 12416), BipartiteDD.IsBipartiteDegDiam H 4 10

Record file: `lean/BipartiteDD/Haar/D4D10b/Record.lean`. Axioms: `lean/BipartiteDD/Haar/D4D10b/Axioms.lean` and
`Axioms.out.txt`, whose only line is `'nb_4_10_12416' depends on axioms: [propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or `extern` in the new files. Certificates are checked
by `decide +kernel`.

## The graph (confirmed first)
- Group `G = Z_97 ⋊_19 Z_64`, order 6,208. Here `19` has order 32 mod 97, which divides 64, so `r^k ≡ 1` holds.
- `S = {(0,0), (74,51), (30,20), (47,1)}` from `research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt`.
- Independent check, a Python BFS script run in the session scratchpad (not committed): the Haar graph on
  `G ⊕ G` (12,416 vertices) is simple and 4-regular, symmetric, and has eccentricity 10 from both `(e,A)` and `(e,B)`.
  Right multiplication is an automorphism, so these two BFS runs bound the diameter by 10.

## Covering (nine letters)
- Word `x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹ x₇ x₈⁻¹ x₉` over `S`, as in `Haar/Diam10.lean`.
- The Python generator checks every code by direct multiplication: all 6,208 elements are covered.
- Stage tables: 16 stages of 388 codes, 18 bits per code (`4^9 = 2^18`), so `16 · 388 = 6,208` exactly.

## Modules (all under `lean/BipartiteDD/Haar/D4D10b/`, namespace `BipartiteDD.Haar.D4D10b`)
- `Words.lean`: `wordOf` (the generic nine-letter word) and `CoverHyp S`, the hypothesis of `Diam10` written with the
  same group operations.
- `Meta97.lean`: the group `Grp`, its `Group` instance, and `equivG : Grp ≃ Fin 6208`.
- `Check.lean`: `sVec`, `sel`, `SS`, `wordD`, `okD`, `chkD`, `stageExD`.
- `Stage00.lean` … `Stage15.lean`: one table per stage, `certDxx : chkD base 388 stageDxx = true := by decide +kernel`.
- `Cover.lean`: `exD` (every `n < 6208` has a code), then `cover : CoverHyp SS`. This uses the `CoverHyp` trick from
  the brief, and it built without an `isDefEq` timeout.
- `Record.lean`: `equiv12416`, the comap graph, and `nb_4_10_12416`, via `haar_isBipartiteDegDiam10_of_equiv`.
- `Axioms.lean`, `Axioms.out.txt`.
- Generator: `research/lean-haarD/gen_d4D10b.py`. It verifies the words, then writes all of the above.

## Build log (one module per `lake build`, sequential, toolchain `leanprover/lean4:v4.34.1`)
- `lake exe cache get` ran in the background, with exit 0 after about 1m45s of system time. elan was installed
  first (`elan-init.sh -y --default-toolchain none`), since no Lean was on the machine.
- Meta97 (5.4 s), Words (1.4 s), Check (1.6 s).
- Stage00 (4.7 s), then Stage01–Stage15, all `rc=0`. Each stage takes about 5 s.
- Cover (2.5 s), Diam10 (2.5 s, built from source, with Haar.Main and Graph), Record (1.0 s).
- Axioms via `lake env lean BipartiteDD/Haar/D4D10b/Axioms.lean`.
- Largest module that built: all 16 stages and the record theorem, so the whole chain builds.

## Deviations from the brief
- Branch: the session's designated branch is `claude/haar-d4d10b-record-kad0cq`, not `lean-haarD-d4D10b`, so all work
  is there.
- The job's `Axioms.lean` and `Axioms.out.txt` sit in `Haar/D4D10b/`. I did not append to the merged `lean/Axioms.lean`,
  since that file imports every record module and regenerating it means building all of them (the same call as
  `LiftA/`).
- The generator is a new file, `gen_d4D10b.py`. I did not add to `gen_lift58410.py`, so the existing record modules
  stay untouched.
- Names are all new: the namespace `BipartiteDD.Haar.D4D10b` (and `…D4D10b.Meta97`) keeps them apart from `LiftA`'s
  `Meta157` and `D4D10`, and no theorem name is reused.
