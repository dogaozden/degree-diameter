# STATUS d8D8: Δ8·D8 record, 225,792 vertices

**Status: done** (the record statement is proved; the check is clean in the sandbox, see caveats).

## Statement
`lean/BipartiteDD/Haar/R225792/Record225792.lean`, `BipartiteDD.Haar.R225792.nb_8_8`:

    ∃ H : SimpleGraph (Fin 225792), BipartiteDD.IsBipartiteDegDiam H 8 8

H is the Haar graph of `G8 = PSL(2,7) × SL(2,7) × Z/2` with the 8-element set S of
`research/frontier/sols/d8D8_prod_psl_7_sl_7_2_s301.txt`, transported along `e2 : G8 ⊕ G8 ≃ Fin 225792`.

## Axioms
`#print axioms` (file `lean/BipartiteDD/Haar/R225792/Axioms.lean`, output in `Axioms.out.txt`):
`[propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide` or `axiom` in the new files.

## Checks in the sandbox
- Vertex count and diameter: `build_haar2.py` on the sol file gives n = 225792, degree 8, ecc 8 from both sides.
- Covering words (A: (S⁻¹S)⁴, B: (SS⁻¹)⁴, C: (SS⁻¹)³S): all 112,896 elements have words; `gen_d8D8.py` re-multiplies every word in G.
- Tables (`TabData`, `TabDefs`, `TabP*`, `TabQ*`, `TabInv`): PSL and SL multiplication and inverse tables checked against the ZMod group by `decide +kernel`, one module per chunk.
- Stages: all 28 stage files `Stage00 … Stage27` compile. Each stage has 16 chunk declarations (`decide +kernel`, 252 elements each).
- `Record225792.lean` compiles (`lake env lean`) against those oleans.

## Largest stage that built
All 28 stages (each 4032 elements in 16 chunks); the largest single declaration is one 252-element chunk.

## Obstacles met (all resolved)
- One declaration checking a full stage (4032 elements) ran out of memory (exit 137), twice. Fixed by one kernel declaration per 252-element chunk.
- A single 4032-element list literal hit Lean's recursion depth. Fixed by writing each stage as 16 literals joined by `++`.
- Table arithmetic in `ZMod 7` was too slow per element. Fixed by checking the group tables once and running stage checks on table indices.
- `TabData.lean` lacked an `import`, so `ℕ` was unknown. Fixed.

## Deviations from the brief
- Branch: the session's designated branch is `claude/lean-haard-d8d8-l0i700`; the brief's `lean-haarD-d8D8` was not used.
- The general Haar lemma (`GraphD.lean` from the "lemma" job) did not exist on any branch, so `lean/BipartiteDD/Haar/Eight.lean` is a self-contained diameter-8 walk lemma (the even case beside `Main.lean`).

## Caveats
- The stage oleans were produced by direct `lean -o` runs (three in parallel, about 9 minutes each), not by `lake build`. A plain `lake build BipartiteDD.Haar.R225792.Record225792` will therefore rebuild the stages from scratch (about 4 h serial). The record is verified by `lake env lean` on the same sources.
- The top-level `lean/Axioms.lean` was not extended, because it imports modules (e.g. `GQST.Main`) that are not built in this sandbox. The record has its own axioms file instead.
