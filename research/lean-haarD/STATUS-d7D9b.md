# STATUS d7D9b: Δ7·D9 record 462,840 vertices (PSL(2,29) × Z19)

**Status: partial, blocked at the last step.** `nb_7_9_haar_462840` does not build yet. Everything below it does.

## Built (one module at a time, `lake build BipartiteDD.Haar.D7D9b.<M>`, all `rc=0`)
- `PSL29`: PSL(2,29) built as `D7D8/PSL19.lean`, with 12180 classes. The numbering facts are checked in
  ten blocks of 1218 indices: one `decide +kernel` over all 12180 indices ran out of memory (exit 137).
- `Base`, `Gens`, `Raw`, `Check`: group `G = PSL29.Grp × Multiplicative (ZMod 19)`, `idxG`/`gOf` into
  `Fin 231420`, the seven generators (`research/frontier/sols/d7D9_psl_29_19_orb3_s1.txt`; `build_haar2.py`
  gives n = 462840, degree 7, diameter 9 from both sides), and the raw arithmetic `Raw.lean` with the proofs that
  it computes the group words (`idxG_wordA`, `idxG_wordB`).
- `Stage00` … `Stage41`: 42 stages of 5510 indices per side, `certA`/`certB` by `decide +kernel` on the raw
  arithmetic (about 110 s per stage; a `ZMod`-based check was 394 s per stage, so the raw form was used).
- `Cover`: `cover1`, `cover2` (the covering hypotheses of `haar_isBipartiteDegDiam9_of_equiv`), stated with
  `wordA`/`wordB` and `eq_of_idxG_eq`.
- Largest stage that built: all 42 stages (`Stage00 … Stage41`).

## Blocked: `Record462840.lean`
- Error: `(deterministic) timeout at isDefEq` at the `cover1` argument of
  `BipartiteDD.Haar.haar_isBipartiteDegDiam9_of_equiv SS haarVert ⟨sel 0, …⟩ cover1 cover2`.
  The application without the cover arguments elaborates in 4 s. The cover argument alone times out at 200000
  heartbeats; `set_option maxHeartbeats 1000000 in` also times out; with heartbeats unbounded the check ran
  for more than 15 minutes without finishing.
- Diagnosis: the cover statements elaborate `⁻¹` and `*` on `G` through Mathlib's product instances
  (`Prod.instInv`, `Prod.instMul`, with `Multiplicative.inv` through `NegZeroClass`). The lemma's `[Group G]`
  gives the `InvOneClass`/`DivisionMonoid` chain over `Prod.instGroup`. The two agree only up to unfolding, and
  `PSL29`'s inverse is `canon …` (a `dite`), so the unifier unfolds it. (`D7D9`, the same lemma with
  `SL(2,31)`, has a structure-literal inverse and elaborates.)
- Tried, none worked: a local `letI : Group G` (the statement still elaborates through `Prod.instInv`); removing
  `Prod.instInv` and `Prod.instMul` from instance scope (the lemma's chain then differs); high-priority
  `Inv G`/`Mul G` instances taken from `Prod.instGroup` (timeout at the same argument). The obtained-variable
  transport `exact ⟨x1, …, h⟩` does elaborate quickly, so the cost is in matching the instance chains.
- Next options: (1) give `G` one instance path that the lemma uses by construction (for example a hand-written
  `Group` instance on `G` whose `inv` and `mul` are the `Prod` operations, with `Multiplicative (ZMod 19)` replaced
  by a type that has only one path). This changes `Base`, so `Raw`, `Check` and all 42 stages rebuild
  (about 80 minutes). (2) Replace `canon` in `PSL29` by a structure-literal inverse, if the sign can be kept
  without `canon`. Option (1) is the sure one.

## Other items
- `Axioms.lean` is in place but `Axioms.out.txt` is not produced, because `nb_7_9_haar_462840` does not exist yet.
- `Record462840.lean` is not in the default library target (as `Record416640.lean`); it does not build in its
  current form (the `set_option maxHeartbeats 1000000 in` line is an attempt, kept for the record).
- Branch: pushed to the designated branch `claude/haar-d7d9-462840-d2uc2u` (not `lean-haarD-d7D9b`), draft PR #252.
- Generator: `research/lean-haarD/gen_d7D9b.py` (SOL, OUTDIR, PSL19 template). The covering words are checked by
  multiplication for all 231420 elements per side; the stage files are reproducible from it.
