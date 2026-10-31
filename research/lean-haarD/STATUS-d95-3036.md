# STATUS d95-3036: the (9,5) record on 3,036 vertices in Lean

**Done.** `nb_9_5_n3036 : ∃ G : SimpleGraph (Fin 3036), BipartiteDD.IsBipartiteDegDiam G 9 5` builds
(`BipartiteDD.Haar.D9D5C69C22.Record3036`). `lean/BipartiteDD/Haar/D9D5C69C22/Axioms.out.txt` reads
`'nb_9_5_n3036' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Graph: the Haar graph of G = C69 : C22 = ⟨x, y | x^69 = y^22 = 1, y x y⁻¹ = x⁸⟩ (y acts with order 22; 8 has order 22 mod 69)
with S = {(0,0), (66,11), (56,11), (28,13), (22,9), (13,15), (64,7), (25,14), (8,8)}, elements x^i y^j written (i,j),
numbering of side A `22 i + j`, side B `1518 + 22 i + j`. Edge file: `research/selfdual-d5/records/d9D5_n3036_haar_c69c22.edges`
(sha256 05305fe9…99051ea9, 13,662 edges, 9-regular; copied unchanged into the Lean folder). Same layout as the (9,5)
2,928 record (`lean/BipartiteDD/Haar/D9D5C61C24/`), with the parameters changed.

## Files (all new; nothing existing changed)

| file | content |
|---|---|
| `lean/BipartiteDD/Haar/D9D5C69C22/Grp.lean` | generated: `Grp` (pairs `ZMod 69 × ZMod 22`), `rpow` with r = 8, the `Group` instance, numbering `enc`/`grpOf`, `equiv1518 : Grp ≃ Fin 1518` |
| `lean/BipartiteDD/Haar/D9D5C69C22/Cert.lean` | generated: `sS`, `SS`, `cert1`, `cert2` (1,518 quadruples each), `ok1`/`ok2` by `decide +kernel`, `cover1`, `cover2` |
| `lean/BipartiteDD/Haar/D9D5C69C22/Record3036.lean` | `equiv3036 : Grp ⊕ Grp ≃ Fin 3036`, `nb_9_5_n3036` (the Haar lemma `haar_isBipartiteDegDiam_of_equiv`) |
| `lean/BipartiteDD/Haar/D9D5C69C22/d9D5_n3036_haar_c69c22.edges` | copy of the edge file (checked byte-identical by the generator) |
| `lean/BipartiteDD/Haar/D9D5C69C22/Axioms.lean`, `Axioms.out.txt` | `#print axioms nb_9_5_n3036` (three standard axioms only) |
| `research/lean-haarD/gen_d9D5_3036.py` | generator of the three Lean files and the edge copy (checks first, see below) |
| `research/lean-haarD/check_d9D5_3036_edges.lean` | `#eval` of the Lean edge list, for the check below |

## Checks before building

1. **Generator (Python, before any Lean file is written):** the group law (`r^(j+b) = r^j r^b` for all j, b; `g g⁻¹ = 1`;
   associativity on a sample); the Haar graph of S on the numbering above is **exactly** the edge file (13,662 edges,
   each side 9-regular, 3,036 vertices); and every element of G has a cover word `a⁻¹ b c⁻¹ d` and one `a b⁻¹ c d⁻¹`
   with a, b, c, d ∈ S (the generator asserts 1,518 entries for each of the two covers).
2. **Lean definitions, after `Cert` was built:** `lake env lean ../research/lean-haarD/check_d9D5_3036_edges.lean` prints the
   edges `(enc g, 1518 + enc (s * g))` computed from `sS`, `enc`, `grpOf` and the `Group` product. Sorted, it is
   byte-identical to the sorted edge file (13,662 lines; every one of the 3,036 vertices has 9 edges).

## Builds (one `lake build <module>` at a time; toolchain `leanprover/lean4:v4.34.1`, Mathlib from the cache)

- `lake build BipartiteDD.Haar.D9D5C69C22.Grp`: ok (4.1 s).
- `lake build BipartiteDD.Haar.D9D5C69C22.Cert`: ok (377 s, `decide +kernel` on 1,518 elements for each cover).
- `lake build BipartiteDD.Haar.D9D5C69C22.Record3036`: ok (15 s, including the Haar modules it imports).
- `lake env lean BipartiteDD/Haar/D9D5C69C22/Axioms.lean`: the axioms line above.
- Grep of the folder for `sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`, `unsafe`, `implemented_by`, `extern`: no matches.

## Choices and deviations from the (9,5) 2,928 record

- Same layout and proof as the 2,928 record, with the numbers changed: `ZMod 69` and `ZMod 22` for the coordinates, r = 8,
  the numbering `(i, j) ↦ 22 i + j`, `Fin 1518` per side, and `equiv3036` from `finSumFinEquiv` with `finCongr`.
- The metacyclic presentation is used as in the 2,928 record. The self-duality and the Cayley form in the README are not used.
- `Cert.lean` has `set_option maxRecDepth 100000 in` on `ok1_all`/`ok2_all`, as in the 2,928 record. No heartbeat limit is raised.
- Toolchain bootstrap in this container: elan and the pinned Lean v4.34.1 were installed, and Mathlib was fetched with
  `lake exe cache get` against the committed `lake-manifest.json`. `lake update` was not run, so the manifest is unchanged.

## Remaining

Nothing. The record is proved; no `sorry` and no open goals.
