# STATUS lift510: Δ5·D10 95,472 in Lean

**Done.** `nb_5_10_95472 : ∃ G : SimpleGraph (Fin 95472), BipartiteDD.IsBipartiteDegDiam G 5 10` builds.
`lean/BipartiteDD/Haar/LiftC/Axioms.out.txt` reads
`'nb_5_10_95472' depends on axioms: [propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `native_decide`, `axiom`, and no `maxHeartbeats` raised in the new files.

## Graph

Haar graph of `Z_1989 ⋊_461 Z_24` (order 47,736), S = the five elements of
`research/lifts/sols/d5D10_n95472_haar_meta1989_24_461.txt`. Confirmed before the proof:
`build.py meta 1989 24 461 0,0 826,18 423,7 1635,11 993,10` and `apsp.c` (all pairs, no symmetry) give
n = 95472, degree 5, bipartite, diameter 10, RESULT VALID.

## Cover

Nine-letter condition `g = x₁ (x₂⁻¹ (… (x₈⁻¹ x₉)))`, `xᵢ ∈ S`, holds for all 47,736 elements. Checked by
`research/lean-haarD/gen_lift510.py`, which enumerates all 5⁹ words, takes the smallest code per element, and
re-evaluates every chosen word with a scalar mirror of the Lean definitions.

## Modules (`lean/BipartiteDD/Haar/LiftC/`)

| Module | Content |
|---|---|
| `Meta1989.lean` | the group, `Grp ≃ Fin 47736` (built) |
| `Check.lean` | `sVec`, `sel`, `wordOf`, `wordG`, `okC`, `chkC` (built) |
| `Stage00…Stage35.lean` | 36 stages of 1,326 indices, each `decide +kernel` (all built, serially, about 15 s each) |
| `Cover.lean` | `exC`: every index has a code (built) |
| `Words.lean` | `CoverHyp`, `cover : CoverHyp SS` (built; the D6D10 fix) |
| `Record95472.lean` | `equiv95472`, `nb_5_10_95472` (built, about 2 s) |
| `Axioms.lean`, `Axioms.out.txt` | the axioms check (three standard axioms) |

## Deviations

- `lean/Axioms.lean` is not extended. Its import closure is 187 modules (older stage tables and records), which
  would take hours to build here. The self-contained `LiftC/Axioms.lean` covers the full dependency closure of
  `nb_5_10_95472`.
- The branch is `claude/lift510-d5d10-lean-wfyuso` (the designated branch), not `lean-haarD-lift510`.
- The commit has no `Co-Authored-By` line naming the model (the system prompt forbids model identifiers in commits).

## Largest stage that built

Stage size 1,326 (36 stages), each about 15 s serially. Whole chain (`Check`, 36 stages, `Cover`, `Words`, record,
axioms) builds in about 12 min of wall time after `lake exe cache get` (about 2 min).

## Build notes

- Toolchain: elan installed from `elan-init.sh`, then `leanprover/lean4:v4.34.1`. Not preinstalled in this container.
- Build one module at a time; `lake build <Module>`. No `-j` flag needed.
