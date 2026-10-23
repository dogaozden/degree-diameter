# STATUS d6D9: Δ6·D9 121,440 in Lean

**Done.** `nb_6_9_haar : ∃ G : SimpleGraph (Fin 121440), IsBipartiteDegDiam G 6 9` builds, with the kernel-checked
certificates for all 60720 elements on both sides. `#print axioms` gives `propext`, `Classical.choice`,
`Quot.sound` only (`lean/BipartiteDD/Haar/D6D9/Axioms.out.txt`). No `sorry`, `admit`, `native_decide`, or `axiom`.

## Graph and check

- `research/frontier/build_haar2.py` on `sols/d6D9_sl_23_5_s401.txt`: n = 121440, degree 6, diameter 9, no
  duplicate edges, valid.
- Group: SL(2,23) × Z5, order 60720. Set S: the six elements of the sol file.

## Modules (all in `lean/BipartiteDD/Haar/`)

| Module | Content |
|---|---|
| `SL23.lean` | SL(2,23) group and numbering `Grp ≃ Fin 12144` (checked on triples and `List.range`) |
| `SL23Z5.lean` | `Grp := SL23.Grp × Multiplicative (ZMod 5)`, numbering `equiv60720 : Grp ≃ Fin 60720` |
| `Diam9.lean` | diameter ≤ 9 for Haar graphs, from eight-letter covers on each side |
| `D6D9/Check.lean` | S, the A/B words, the bit-packed table reader `codeAt`, checkers `chkA`/`chkB` |
| `D6D9/Stage00..11.lean` | certificate tables, 5060 indices per stage, `certA k` and `certB k` by `decide +kernel` |
| `D6D9/Cover.lean` | `cover1`, `cover2`: every element is an 8-letter A-word / B-word in `SS` |
| `Record121440.lean` | `nb_6_9_haar` |

Certificates come from `research/lean-haarD/gen_d6D9.py`. Each element gets four pairs (eight letters of S) per side.
The script re-checks every word by direct multiplication. The Lean stage generator is deterministic (regeneration
gives byte-identical `Stage00.lean`).

## Obstacles met and how they were resolved

1. **Full quadruple enumeration over `ZMod 23`** (279,841 tuples for `enc_bound`/`quad_enc`): the kernel build was
   OOM-killed (exit 137, about 6 GB then 13 GB). Replaced by per-case checks over triples (`quad_enc0`,
   `quad_enc1`, 12,167 cases each) plus `omega` for the bound.
2. **`∀ n < 12144` decide** (`det_quad`, `enc_quad`): the elaborated `Nat.decidableBallLT` used 13 GB. Replaced
   by `(List.range N).all … = true := by decide +kernel`.
3. **5060-entry list literals** per table: "maximum recursion depth" in the elaborator, 3.5 min per attempt.
   Replaced by one packed `ℕ` literal per table (21 bits per code, hex), read by `codeAt C i = (C >>> 21 i) % 2^21`.
4. **Parallel stage builds**: 4 concurrent `lake build` jobs were OOM-killed (exit 137). Stages were built one at
   a time instead.

## Largest stage that built

All of it. Each stage (5060 indices, A and B) takes about 210–225 s and peaks at about 2.3–3.5 GB. The full chain
`Record121440` (after all 12 stages) builds with `lake build BipartiteDD.Haar.Record121440` (~2 s on top of the stages).

## Deviations from the brief

- **Lemma job.** `lean-haarD-lemma` / `GraphD.lean` is not on origin. `Diam9.lean` is a local diameter-9 lemma
  for four-pair covers. It is not a general `GraphD` form.
- **Branch.** The job names `lean-haarD-d6D9`. The session's designated branch is `claude/lean-haard-d6d9-g3pgua`,
  and that is where the work is pushed. Draft PR: https://github.com/dogaozden/degree-diameter/pull/233
- **Global axioms file.** `lean/Axioms.lean` and its `Axioms.out.txt` are not updated, because regenerating them
  needs a full repo build that was not run. The record's own axiom output is committed in `D6D9/Axioms.out.txt`.
- **Not in the default library target.** `Record121440` is not imported by `BipartiteDD.lean`/`Records.lean`,
  so a default `lake build` does not build it.
- **Vertex-count proof.** `equiv121440` gives `Grp ⊕ Grp ≃ Fin 121440` from `equiv60720`, so the count is proved
  rather than assumed.

## Timing

Stage 00 first built in 217 s. Stages 01–11 built serially in 209–227 s each. The full run was about 45 minutes of
build time, plus the failed attempts described above.
