# lean-haarD job d8D8d: Δ8·D8 record 239,904 (PSL(2,17) × Z49)

**Status: done.** `nb_8_8_239904` builds, and `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.

## Result

- Theorem: `nb_8_8_239904 : ∃ H : SimpleGraph (Fin 239904), BipartiteDD.IsBipartiteDegDiam H 8 8`
  in `lean/BipartiteDD/Haar/D8D8b/Record.lean`. Same existential form as `nb_9_8`, `nb_7_9_haar`, `nb_8_7_haar`.
- Graph: Haar graph of G = PSL(2,17) × Z49 (|G| = 119,952) with the 8-element set of
  `research/frontier/sols/d8D8_psl_17_49_orb3_s1.txt`; 2 × 119,952 = 239,904 vertices.
- Axioms: `lean/BipartiteDD/Haar/D8D8b/Axioms.lean` and `Axioms.out.txt` (`propext, Classical.choice, Quot.sound`).
  An entry for `nb_8_8_239904` was also added to the top-level `lean/Axioms.lean` (import plus `#print`), with its
  verified line appended to `lean/Axioms.out.txt`. The top-level file was **not** fully regenerated: it imports many
  project modules that are not built in this sandbox, so only the new line was verified.
- Forbidden content: `grep` over `lean/BipartiteDD/Haar/D8D8b/` finds no `sorry`, `admit`, `native_decide`, or `axiom`.
  Every covering check is `decide +kernel` or `decide`, as in the D7D8b pattern.

## Modules

Built one at a time with `lake build <Module>`, in this order:

- `D7D8.Diam8` (shared diameter-8 lemma, from master), `D8D8b.PSL17`, `Base`, `Gens`, `Check`
- `CertAA0..48`, `CertAB0..48`, `CertBB0..48` (147 stage modules, each about 55–70 s; 49 chunks of 2448 codes each)
- `Cover`, `Covers`, `Record`, `Axioms`

Stage driver: `research/lean-haarD/d8D8b/build_stages.sh`. It is resumable: each call builds until a time budget
runs out, skips modules already logged OK, and stops at the first failure. The whole run took about 2.5 hours
of build time on this sandbox (estimated from the per-stage times; 4 cores, 15 GB RAM, no parallel builds).

## Certificate generator

`research/lean-haarD/d8D8b/gen_d8D8b.py SOL [CHUNK] [OUTDIR]` regenerates `Gens`, `Cover`, and all 147 `Cert*`
modules from the sol file. Regenerating from the sol file gives output byte-identical to the committed modules.
It re-multiplies every covering word in Python (all 119,952 elements verified).

## What was reused

- The checkpoint branch `claude/haar-psl-17-49-record-d8d8c-uupxw3` (commit `d36d176a8`): its `D8D8b` tree and
  generator were imported onto a branch from `origin/master`, then verified by regenerating and rebuilding.
  The other prior branch (`y3r7u5`) was not used.
- Master's `D7D8b` pattern for `Covers`, `Check`, `Cover` glue, and `Record`. Master's `D7D8/Diam8.lean` supplies the
  diameter-8 lemma (`isBipartiteDegDiam_eight_equiv`).

## Branch and attribution

- Work is on the designated branch `claude/haar-d8d8-record-239904-94jf51`, not `lean-haarD-d8D8d` as the brief
  suggests: the session instructions name the designated branch.
- Commit messages carry `Co-Authored-By: Claude <noreply@anthropic.com>` and the session URL, without a model name:
  the operator rule forbids model identifiers in pushed artifacts.

## Obstacles

None remaining. The toolchain was not preinstalled. It was installed with elan (`leanprover/lean4:v4.34.1`) and
`lake exe cache get` fetched 8,908 mathlib files.
