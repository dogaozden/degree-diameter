# STATUS d95-2928: the (9,5) record on 2,928 vertices in Lean

**Done.** `nb_9_5_n2928 : ∃ G : SimpleGraph (Fin 2928), BipartiteDD.IsBipartiteDegDiam G 9 5` builds
(`BipartiteDD.Haar.D9D5C61C24.Record2928`). `lean/BipartiteDD/Haar/D9D5C61C24/Axioms.out.txt` reads
`'nb_9_5_n2928' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Graph: the Haar graph of G = C61 : C24 = ⟨x, y | x^61 = y^24 = 1, y x y⁻¹ = x^14⟩ (y acts with order 6) with
S = {(0,0), (19,0), (42,12), (59,4), (35,20), (54,7), (30,5), (57,14), (56,10)}, elements x^i y^j written (i,j),
numbering of side A `24 i + j`, side B `1464 + 24 i + j`. Edge file: `research/selfdual-d5/records/d9D5_n2928_haar_c61c24.edges`
(sha256 b018047d…d75ecd233, 13,176 edges, 9-regular; copied unchanged into the Lean folder). The same layout as the (7,5)
1,312 record (`lean/BipartiteDD/Haar/D7D5C41C16/`).

## Files (all new; nothing existing changed)

| file | content |
|---|---|
| `lean/BipartiteDD/Haar/D9D5C61C24/Grp.lean` | generated: `Grp` (pairs `ZMod 61 × ZMod 24`), `rpow`, the `Group` instance (product `(i,j)(a,b) = (i + r^j a, j + b)`), numbering `enc`/`grpOf`, `equiv1464 : Grp ≃ Fin 1464` |
| `lean/BipartiteDD/Haar/D9D5C61C24/Cert.lean` | generated: `sS`, `SS`, `cert1`, `cert2` (1,464 quadruples each), `ok1`/`ok2` by `decide +kernel`, `cover1`, `cover2` |
| `lean/BipartiteDD/Haar/D9D5C61C24/Record2928.lean` | `equiv2928 : Grp ⊕ Grp ≃ Fin 2928`, `nb_9_5_n2928` (the Haar lemma `haar_isBipartiteDegDiam_of_equiv`) |
| `lean/BipartiteDD/Haar/D9D5C61C24/d9D5_n2928_haar_c61c24.edges` | copy of the edge file (checked identical by the generator) |
| `lean/BipartiteDD/Haar/D9D5C61C24/Axioms.lean`, `Axioms.out.txt` | `#print axioms nb_9_5_n2928` (three standard axioms only) |
| `research/lean-haarD/gen_d9D5_2928.py` | generator of the three Lean files and the edge copy (checks first, see below) |
| `research/lean-haarD/check_d9D5_2928_edges.lean` | `#eval` of the Lean edge list, for the check below |

## Checks before building

1. **Generator (Python, before any Lean file is written):** the group law (`r^(j+b) = r^j r^b` for all j, b; `g g⁻¹ = 1`;
   associativity on a sample); the Haar graph of S on the numbering above is **exactly** the edge file (13,176 edges,
   each side 9-regular, 2,928 vertices); and every element of G has a cover word `a⁻¹ b c⁻¹ d` and one `a b⁻¹ c d⁻¹`
   with a, b, c, d ∈ S (the generator asserts 1,464 entries for each of the two covers).
2. **Lean definitions, after `Cert` was built:** `lake env lean ../research/lean-haarD/check_d9D5_2928_edges.lean` prints the
   edges `(enc g, 1464 + enc (s * g))` computed from `sS`, `enc`, `grpOf` and the `Group` product. Sorted, it is
   byte-identical to the sorted edge file (13,176 lines; every one of the 2,928 vertices has 9 edges).

## Builds (one `lake build <module>` at a time; toolchain `leanprover/lean4:v4.34.1`, Mathlib from the cache)

- `lake build BipartiteDD.Haar.D9D5C61C24.Grp`: ok (2.6 s).
- `lake build BipartiteDD.Haar.D9D5C61C24.Cert`: ok (207 s, `decide +kernel` on 1,464 elements for each cover).
- `lake build BipartiteDD.Haar.D9D5C61C24.Record2928`: ok (the Haar modules it imports build from source in about 8 s).
- `lake env lean BipartiteDD/Haar/D9D5C61C24/Axioms.lean`: the axioms line above.
- Grep of the folder for `sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`, `unsafe`, `implemented_by`, `extern`: no matches.

## Choices and deviations from the (7,5) 1,312 record

- The group is written by hand, as in the (7,5) record: a structure with a `Group` instance and `rpow_add` by `decide +kernel`
  over `ZMod 24 × ZMod 24`. The numbering `G ≃ Fin 1464` is `(i, j) ↦ 24 i + j`, the same as the edge file, so `equiv2928`
  is `finSumFinEquiv` with no reindexing.
- `Cert.lean` has `set_option maxRecDepth 100000 in` on `ok1_all`/`ok2_all`, as in the (7,5) record. No heartbeat limit is raised.
- The `SmallGroup(1464,1)` id mentioned in `research/selfdual-d5/README.md` is not used or checked in Lean; the proof uses only the
  metacyclic presentation. The self-dual and Cayley structure of the README is not needed for the proof, which uses the Haar lemma only.
- As for the (7,5) record, the theorem is top-level and is not imported by `BipartiteDD.lean`.
- Toolchain bootstrap in this container: elan and the pinned Lean v4.34.1 were installed, and Mathlib was fetched with
  `lake exe cache get` against the committed `lake-manifest.json`. `lake update` was not run, so the manifest is unchanged.

## Remaining

Nothing. The record is proved; no `sorry` and no open goals.
