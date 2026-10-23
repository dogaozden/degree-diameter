# Job d6D8: Lean proof of the Δ6·D8 record (30,576 vertices)

**Status: done.**

## Result

`BipartiteDD.Haar.SL213Z7.nb_6_8 : BipartiteDD.IsBipartiteDegDiam G30576 6 8`, where `G30576` is the Haar graph of
`SS` (the six elements of `research/frontier/sols/d6D8_sl_13_7_s1.txt`) on `Fin 30576`, transported by
`equiv30576 : Gp ⊕ Gp ≃ Fin 30576`. `nb_6_8_exists` gives the `∃ G` form.

- Vertex count: `research/frontier/build_haar2.py` on the sol file gives n = 30576, degree 6, ecc 8 from both sides, VALID.
- Axioms (`lean/Axioms.lean`, `lean/Axioms.out.txt`): `propext, Classical.choice, Quot.sound` only. No `sorry`,
  `admit`, `axiom` or `native_decide`; the kernel checks use `decide +kernel`.

## Modules (lean/BipartiteDD/Haar/)

| module | content |
|---|---|
| `SL213.lean` | SL(2,13) as `Grp`, numbering `enc`/`grpOf` of the 2184 elements, checks by `decide +kernel` |
| `SL213Z7.lean` | `Gp = SL(2,13) × Multiplicative (ZMod 7)`, `enc7`/`grpOf7` (15288 elements), `equiv30576` |
| `Diam8.lean` | `diam8_of`: diameter ≤ 8 for a Haar graph from three covering hypotheses (A–A, B–B words of length 4; A–B words of length 3 plus one step). Same walk construction as `Main.lean` |
| `Cert30576Gens.lean` | the six generators `sS`, `SS`, and the predicates `okA`, `okB`, `okAB` |
| `Cert30576_0..14.lean` | certificate stages, 1024 entries each (last one 952), checked by `decide +kernel` |
| `Record30576.lean` | cover lemmas (dispatch over the 15 stages), `G30576`, `nb_6_8` |

Generator: `research/lean-haarD/make_cert_d6d8.py`. It BFS-finds shortest covering words for all 15288 elements
(depth 4 for A and B, depth 3 for AB) and multiplies each word out in Python before writing the Lean data.

## Build

- Each stage module is built on its own (`lake build BipartiteDD.Haar.Cert30576_<k>`). Stage 0 took about 200 s
  (`decide +kernel` over 1024 entries × 3 predicates). All 15 stages and `Record30576` built with exit 0.
- Largest stage that built: all of them (1024 entries per stage; the one-piece version was not attempted).

## Deviations from the brief

- Branch: the brief names `lean-haarD-d6D8`; the session's designated branch is `claude/lean-haar-d6d8-4txh6f`,
  which is where the work is pushed.
- The `lemma` job's `GraphD.lean` did not exist on origin, so the diameter-8 lemma is `Haar/Diam8.lean`, written for
  this record only (not the general even/odd statement).
- `Axioms.out.txt`: only the two new lines were appended, from a scratch file that imports `Record30576`; the whole
  file was not regenerated.
