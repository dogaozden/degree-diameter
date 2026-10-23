# STATUS d8D7: Δ8·D7 record, 41,040 vertices

**Status: done.** The record statement is proved, all modules build with `lake build`, and the axioms are the three standard ones.

## Statement
`lean/BipartiteDD/Haar/Record41040.lean`, `BipartiteDD.Haar.D8D7.nb_8_7_haar`:

    ∃ G : SimpleGraph (Fin 41040), BipartiteDD.IsBipartiteDegDiam G 8 7

G is the Haar graph of `SL(2,19) × Z_3` (order 20520) with the 8-element set S of
`research/frontier/sols/d8D7_sl_19_3_s2.txt`, transported along `equiv41040 : (G ⊕ G) ≃ Fin 41040`.

## Axioms
`lean/BipartiteDD/Haar/D8D7/Axioms.lean`, output in `Axioms.out.txt`:

    'nb_8_7_haar' depends on axioms: [propext, Classical.choice, Quot.sound]

No `sorry`, `admit`, `native_decide` or `axiom` in the new files (grep checked).

## Pieces
- `Haar/SL19.lean`: SL(2,19) numbering (342 elements with c = 0, then 6498 with c ≠ 0), same construction as `SL23.lean`.
  Its `decide +kernel` checks (`det_quad_all`, `enc_quad_all`, `quad_enc0`, `quad_enc1`) pass.
- `Haar/SL19Z3.lean`: `SL(2,19) × Z_3`, index `3 * enc g + z`, `equiv20520`.
- `Haar/Diam7.lean`: the diameter-7 lemma with three-pair covers (A-to-A and B-to-B within 6, A-to-B within 7).
  It mirrors `Diam9.lean` and does not use the odd-case lemma of `GraphD.lean` (see deviations).
- `Haar/D8D7/Check.lean`: S as `sVec`, the words `wordA`, `wordB` (six letters, base-8 codes, 18 bits), `chkA`, `chkB`.
- `Haar/D8D7/Stage00.lean … Stage11.lean`: 12 stages of 1710 elements, each with `certA` and `certB` checked by `decide +kernel`.
- `Haar/D8D7/Cover.lean`: `cover1`, `cover2`, the covering hypotheses for every element of the group.
- `research/lean-haarD/gen_d8D7.py`: the generator. It rebuilds the group numbering, finds 3-pair words for all 20520 elements on both sides, and re-multiplies every word in G before writing the Lean files.

## Checks in the sandbox
- `build_haar2.py` on the sol file: n = 41040, degree 8, ecc 7 from both sides, no unreached vertices.
- `gen_d8D7.py`: group numbering checked; every element of G has an A-word and a B-word of three pairs (BFS coverage and direct multiplication).
- Each stage module was built with `lake build -j` one module at a time (`lake build BipartiteDD.Haar.D8D7.Stage00` etc.), in order, with no failures. Each stage took about 55 s.

## Largest stage that built
All 12 stages (1710 elements each, A and B tables) and `Cover` and `Record41040` built. The largest kernel declaration is one stage check of 1710 codes.

## Deviations from the brief
- Branch: the session's designated branch `claude/lean-haar-d8d7-ecb54e` was used, not `lean-haarD-d8D7`. The draft PR is #240.
- `Diam7.lean` is a standalone copy of the `Diam9` argument for n = 3, not a use of `GraphD.lean`'s `haar_ediam_le_odd`. Both prove the same bound. The standalone version was chosen because it reuses the `e : G ⊕ G ≃ W` transport that the existing `Record` files already use.
- The commit trailer names no model, per the repository rule. The attribution line the reminder asked for was omitted for that reason.

## Caveats
- The stage oleans were produced by `lake build` in the sandbox. The `lake build BipartiteDD.Haar.Record41040` run used the already built stages, so the record is verified by a normal build.
- The top-level `lean/Axioms.lean` was not extended. The record has its own axioms file, as in `D6D9`.
