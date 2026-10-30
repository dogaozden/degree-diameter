# STATUS d75-1312: the (7,5) record on 1,312 vertices in Lean

**Done.** `nb_7_5_n1312 : ∃ G : SimpleGraph (Fin 1312), BipartiteDD.IsBipartiteDegDiam G 7 5` builds
(`BipartiteDD.Haar.D7D5C41C16.Record1312`). `lean/BipartiteDD/Haar/D7D5C41C16/Axioms.out.txt` reads
`'nb_7_5_n1312' depends on axioms: [propext, Classical.choice, Quot.sound]`.

Graph: the Haar graph of G = C41 : C16 = ⟨x, y | x^41 = y^16 = 1, y x y⁻¹ = x^38⟩ (SmallGroup(656,28)) with
S = {(0,0), (3,8), (18,8), (14,3), (1,5), (32,14), (1,2)}, elements x^i y^j written (i,j), numbering of side A
`16 i + j`, side B `656 + 16 i + j`. Edge file: `research/d75-raise/records/d7D5_n1312_haar_c41c16.edges`
(sha256 95642aa9…53b73, 4,592 edges, 7-regular). The same layout as the 1,200 record (`lean/BipartiteDD/Haar/D7D5SL5/`).

## Files (all new; nothing existing changed)

| file | content |
|---|---|
| `lean/BipartiteDD/Haar/D7D5C41C16/Grp.lean` | generated: `Grp` (structure of pairs `ZMod 41 × ZMod 16`), `rpow`, the `Group` instance (product `(i,j)(a,b) = (i + r^j a, j + b)`), numbering `enc`/`grpOf`, `equiv656 : Grp ≃ Fin 656` |
| `lean/BipartiteDD/Haar/D7D5C41C16/Cert.lean` | generated: `sS`, `SS`, `cert1`, `cert2` (656 quadruples each), `ok1`/`ok2` by `decide +kernel`, `cover1`, `cover2` |
| `lean/BipartiteDD/Haar/D7D5C41C16/Record1312.lean` | `equiv1312 : Grp ⊕ Grp ≃ Fin 1312`, `nb_7_5_n1312` (the Haar lemma `haar_isBipartiteDegDiam_of_equiv`) |
| `lean/BipartiteDD/Haar/D7D5C41C16/Axioms.lean`, `Axioms.out.txt` | `#print axioms nb_7_5_n1312` (three standard axioms only) |
| `research/lean-haarD/gen_d7D5_1312.py` | generator of the three Lean files (checks first, see below) |
| `research/lean-haarD/check_d7D5_1312_edges.lean` | `#eval` of the Lean edge list, for the check below |

## Checks before building

1. **Generator (Python, before any Lean file is written):** the group law (`r^(j+b) = r^j r^b` for all j, b; `g g⁻¹ = 1`;
   associativity on a sample), and the Haar graph of S on the numbering above is **exactly** the edge file: 4,592 edges,
   each side 7-regular, 1,312 vertices.
2. **Lean definitions, after `Cert` was built:** `lake env lean research/lean-haarD/check_d7D5_1312_edges.lean` prints the
   edges `(enc g, 656 + enc (s * g))` computed from `sS`, `enc`, `grpOf` and the `Group` product. Sorted, it is
   byte-identical to the sorted edge file (4,592 lines; every A-vertex has 7 edges).

## Builds (one `lake build <module>` at a time; toolchain `leanprover/lean4:v4.34.1`, Mathlib cache fetched)

- `lake build BipartiteDD.Haar.D7D5C41C16.Grp`: ok (3 s, after the `ZMod` import was added; first attempt failed on that import only).
- `lake build BipartiteDD.Haar.D7D5C41C16.Cert`: ok (54 s, `decide +kernel` on 656 elements for each cover).
- `lake build BipartiteDD.Haar.D7D5C41C16.Record1312`: ok (the Haar modules it imports build from source in about 10 s).
- `lake env lean BipartiteDD/Haar/D7D5C41C16/Axioms.lean`: the axioms line above.
- Grep of the folder for `sorry`, `admit`, `axiom`, `native_decide`, `maxHeartbeats`, `unsafe`, `implemented_by`, `extern`: no matches.

## Choices and deviations from the 1,200 record

- The group is written by hand (a structure with a `Group` instance, `rpow_add` by `decide +kernel`), not taken from a Mathlib
  semidirect product; there is no metacyclic group in the repo, and the hand-written one keeps the kernel computations of
  the covers as simple as in the 1,200 case. I did not try a semidirect product.
- The numbering `G ≃ Fin 656` is `(i, j) ↦ 16 i + j`, the same as the edge file, so `equiv1312` is `finSumFinEquiv` with no
  reindexing. The 1,200 folder has no adjacency table; the edge check above is the Lean-side check that the numbering and
  S produce the edge file.
- `Cert.lean` has `set_option maxRecDepth 100000 in` on `ok1_all`/`ok2_all`, as the 1,200 `Cert.lean` does. No heartbeat limit is raised.
- As for the 1,200 record, the theorem is top-level and is not imported by `BipartiteDD.lean`.

## Remaining

Nothing. The record is proved; no `sorry` and no open goals.
