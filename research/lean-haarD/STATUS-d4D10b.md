# STATUS d4D10b: Δ4·D10 12,416 in Lean

**Done.** `nb_4_10_12416` builds, and `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`.

- Record: `lean/BipartiteDD/Haar/D4D10b/Record.lean`, `theorem nb_4_10_12416 : ∃ H : SimpleGraph (Fin 12416), BipartiteDD.IsBipartiteDegDiam H 4 10`.
- Graph: Haar graph of `G = Z_97 ⋊_19 Z_64` (order 6,208), with `S = {(0,0), (74,51), (30,20), (47,1)}` from
  `research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt`. Vertices are `G ⊕ G ≃ Fin 12416`.
- Diameter: `haar_isBipartiteDegDiam10_of_equiv` (`Haar/Diam10.lean`), with the nine-letter cover `coverD`. The
  pattern is that of `LiftA/D4D10` (nb_4_10_12246), which is the copy source.
- Certificate: `research/lean-haarD/gen_d4D10b.py` (imports the templates of `gen_lift58410.py`). It checks all
  6,208 indices by direct multiplication before writing. Words are base-4 codes of 9 letters, 16 stages of 388
  entries each (18-bit codes, `decide +kernel` per stage).
- Axioms: `lean/BipartiteDD/Haar/D4D10b/Axioms.lean` and `Axioms.out.txt`.

## Build order (one module at a time, all passed)

`Meta97` (8.5 s), `Diam10` (3.6 s; its import chain built in about 18 s), `Check` (3.3 s), `StageD00` … `StageD15`
(about 8–10 s each, about 2.5 min in total), `Cover` (4.5 s), `Record` (3.1 s), `Axioms` (`lake env lean`, 4.7 s).

All 16 stage modules, `Cover`, and `Record` built, so the largest stage is the whole certificate. There was no `isDefEq` timeout on the cover
argument, so the `CoverHyp` / `wordOf` workaround from `STATUS-d6D10c.md` was not needed.

## Independent check

`research/lean-haarD/check_d4D10b.py` (run as `python3 -I`)
builds the same graph from the sol file alone (no Lean). It checks 12,416 vertices, degree 4, bipartite, and
diameter 10. Right multiplication by `G` is an automorphism, so the two BFS runs from `inl 0` and `inr 0`
(eccentricity 10 each) give the full diameter.

## Notes

- Branch: `claude/d4d10-haar-lift-ubpe8m` (the designated branch for this session), not `lean-haarD-d4D10b`.
- `lake exe cache get` was run first. The toolchain was installed with elan (leanprover/lean4:v4.34.1).
