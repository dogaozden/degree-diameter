# lean-d5: status

Branch claude/d5-formalization-6yt0dm. Files: lean/BipartiteDD/LeanMaxx/D5/. Builds: `lake build BipartiteDD.LeanMaxx.D5.<Module>`.
The toolchain is not preinstalled in the cloud container: elan from github.com/leanprover/elan, then `lake exe cache get` in lean/.

| target | statement | file | status |
|---|---|---|---|
| base | F1–F3 of the note (all pairs within 4, different colours within 3, two neighbours, covering lemma) | Base.lean | done |
| 1 | Theorem A: level graph, any tournament/typing/bijections, diameter ≤ 5 (`Hyp.theoremA`, route form `Hyp.repaired_of_empty`) | Level.lean, ThmA.lean | done (axioms: see Axioms.out.txt when written) |
| 2 | Theorems 3.5/3.6: distance part (`Hyp.ediam_le_five`, `Hyp.ediam_le_five_of_repaired`) | ThmA.lean | done |
