# VERIFY: omega3 (Theorem 3.3 of research/theorems/OMEGA_REPAIR.md, Lean files `lean/BipartiteDD/LeanMaxx/Omega3/`)

Job leanmaxx-verify-omega3 (independent verifier, Sonnet). Verifier branch `claude/leanmaxx-verify-omega3-jas79g`, made
from origin/master (ab2f6fb), with `origin/claude/thm-omega3-formalization-r197t8` (ecb86fb) merged. I did not use the
worker's logs or its `Axioms.out.txt` as evidence, and I changed no proof. Extra files of mine are under
`research/lean-maxx/verify-omega3/` and are not part of the Lean library.

## Verdict

**The proof is accepted, and the headline theorems state Theorem 3.3.** Every Omega3 module builds from a clean
checkout with Lean 4.34.1 and Mathlib, with no sorry. The regenerated axiom list is byte-identical to the committed
one and shows only `propext`, `Classical.choice`, `Quot.sound`. The statements say what Theorem 3.3 says (q ≥ 8, every
finite field, reading 2 and its dual, every block pattern, every labelling whose transfers are automorphisms of the
incidence graph; conclusion: diameter ≥ 9), with the limits listed in §5. None of them weakens Theorem 3.3 as the note
states it. The part of the note's Theorem 3.3 that gives explicit numbers of far vertices per hub is not stated in Lean
(§5.3).

## 1. Merge

`git merge --no-ff origin/claude/thm-omega3-formalization-r197t8` into the branch at origin/master: **no conflicts**.
The branch adds 30 files (12 Lean files under `Omega3/`, the copied `Omega2/` (10 files) and `Projection/` (4 files),
and four notes under `research/lean-maxx/`). `git diff --name-status origin/master HEAD` shows only additions; no
existing file is modified.

## 2. Build, one module at a time, foreground

Fresh container: no `.lake`, no Lean. I installed elan, toolchain `leanprover/lean4:v4.34.1` (the repo's
`lean-toolchain`), ran `lake exe cache get` (8,908 Mathlib files), then `lake build <module>` in dependency order,
each in the foreground:

| module | result | time |
|---|---|---|
| `Omega3.Balls` (also built `Doubling.Hat`, `Omega2.Sphere`) | OK, 1 linter warning (`haveI`) | 31 s |
| `Omega3.Wiring` | OK | 22 s |
| `Omega3.Tables` (`decide +kernel` for q = 8, 9) | OK | **5 min** |
| `Omega3.Graph` | OK | 32 s |
| `Omega3.Route` | OK | 19 s |
| `Omega3.Shape` | OK | 20 s |
| `Omega3.Main` | OK | 22 s |
| `Omega3.Geometric` | OK | 20 s |
| `Omega3.Shared` | OK | 18 s |
| `Omega3.Concrete` (also built `Omega2.Polygon`, `Hexagon.*`, `HexagonEven.*`) | OK, linter warnings only | 2 min 15 s |
| `Omega3.Axioms` | OK | 17 s |

Every build exited 0. No log contains `sorry` or "declaration uses". The warnings are style linters (`haveI` vs
`have`, unused simp arguments, unused section variables, in the older `Hexagon` files too). The Omega3 files import
nothing from `Projection/`.

## 3. Axioms

`lake env lean BipartiteDD/LeanMaxx/Omega3/Axioms.lean` (17 `#print axioms` lines: the two ball bounds, `card_F0_le`,
`star_small`, `star_exists`, `walk_route`, `shape`, `omega3_far`, `omega3_ediam`, `omega3_geometric`,
`geometric_of_shared`, `omega3_geometric_shared`, `hex_hexagon`, `omega3_hexagon`, `omega3_hexagon_geometric`,
`omega3_hexagon_geometric_shared`, `omega3_hexagon_thesis`). Output saved as
`research/lean-maxx/verify-omega3/Axioms.regen.txt`. `diff` against the committed
`lean/BipartiteDD/LeanMaxx/Omega3/Axioms.out.txt`: **identical**. All 17 lines read
`[propext, Classical.choice, Quot.sound]`. These theorems depend on `Hexagon.*`, `HexagonEven.*` and `Doubling.Hat`
from master; the lists are transitive, so those are covered.

## 4. Grep over `Omega3/*.lean`

Searched for: sorry, admit, axiom, native_decide, implemented_by, extern, unsafe, ofReduceBool, opaque, instance,
set_option, macro, elab, syntax, notation, attribute, partial, `#eval`, `#exit`, `Lean.`, `decide +native`, `@[`.

| term | hits | explanation |
|---|---|---|
| sorry, admit, native_decide, implemented_by, extern, unsafe, ofReduceBool, opaque, instance, macro, elab, syntax, notation, partial, `#eval`, `#exit`, `Lean.` | 0 | |
| axiom | 1 | the word in a comment, `Tables.lean:8` ("it adds no axiom") |
| set_option | 19 | `linter.unusedSectionVars false` and `linter.style.longLine false` (2 per file, style only) and `maxRecDepth 100000` in `Tables.lean:12` (needed by the kernel evaluation; adds no axiom) |
| `decide +kernel` | 11 | `Tables.lean`, one per `tabN_k` theorem: kernel evaluation of a decidable proposition over `Fin α → Bool`. `#print axioms star_exists` shows no `Lean.ofReduceBool`, so it is the kernel, not the compiler |
| `@[` | 2 | `@[simp]` on `hubcol_false`, `hubcol_true` |
| noncomputable | 6 | `opp`, `X2`, `X4`, `T3`, `ballOpp`, `covSet`; definitions over `Finset.filter` with classical decidability |

## 5. Statement fidelity

### 5.1 The headline theorem

`omega3_hexagon_geometric_shared` (`Concrete.lean:88`), printed by `#check` in my `Check.lean`:

    ∀ {F : Type u_1} [Field F] [Fintype F], 8 ≤ Fintype.card F →
      ∀ {α : ℕ}, 0 < α → 2 * α ≤ Fintype.card F + 3 →
        ∀ (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm (SPt F ⊕ HLine F)),
          (∀ c u, klass (μ c u) = klass u) →
          GeometricShared typ (incGraph hexInc) klass ε₀ μ →
          9 ≤ (omega (incGraph hexInc) klass typ ε₀ (labMk μ)).ediam

Compared with Theorem 3.3 and the §1.2 model of the note:

| item in the note | in Lean | verdict |
|---|---|---|
| q ≥ 8, `q = |F|`, any finite field | `[Field F] [Fintype F]`, `8 ≤ Fintype.card F`; `hex_hexagon` proves `Hex` for every finite field via `HexagonEven.genPolygonGraph_hexagon_even` (no characteristic hypothesis) | matches; covers q = 8, 9, 11, 13, 16, … |
| H(q) | `SPt F` (singular points of x₀x₄+x₁x₅+x₂x₆−x₃²), `HLine F` (2-spaces on which all pairs satisfy Tits' six equations), `hexInc`; I read `Hexagon/Defs.lean` and rebuilt it independently (§6) | matches |
| α blocks of five copies; α = ⌊(q+3)/2⌋ | `α` free with `0 < α`, `2α ≤ q+3`; Gómez's α satisfies it (`gomez_alpha` in my `Check.lean`, one line) | **more general** than the note |
| block type a/b | `typ : Fin α → Bool`, any pattern | matches ("any block pattern") |
| wiring table | `metPos`: a unbarred {k−1,k+1}, a barred {k+2,k+3}, b unbarred {k+3,k+4}, b barred {k−1,k+1} | matches §1.2 symbol for symbol |
| hubs: one per row, `(t,k)`, `(t,k̄)`, degree 2α | `Hub` = (bar, k, row r of colour `hubcol ε₀ bar`); joined to the mark `mk bar c r` of every copy it meets | matches. The graph has exactly the vertices of the note (5α·2N copy vertices, 10N hubs: 60N = 2,246,940 at q = 8, as in the referee's table) |
| reading 2 and its dual | `ε₀ = 0` (unbarred hubs on points), `ε₀ = 1` (unbarred on lines) | matches the note's §4 wording |
| labelling: P_c, L_c bijections per copy, shared by the hub classes of a bar meeting the copy | `μ c : Perm (SPt ⊕ HLine)` colour-preserving, `labMk μ = fun _ c => μ c`; a colour-preserving permutation is exactly a pair (point map, line map) | matches the per-copy model the referee asks the note to name |
| geometric: every transfer T_Y(c→d) of a class Y meeting c and d is the restriction of an element of Aut(I) | `GeometricShared`: for all bar, k, copies c, d met by (bar,k): ∃ g, `IsAut g` ∧ ∀ row r of the class colour, `μ d r = g (μ c r)` | matches. `IsAut` is any graph automorphism, so collineations, and dualities when q = 3^e, are both allowed; no claim is made about the shape of Aut(I) |
| conclusion: diameter ≥ 9 | `9 ≤ (omega …).ediam` in `ℕ∞` | matches; `ediam = ⊤` also satisfies it. Connectivity is not claimed. "No diameter-8 graph" is what the note needs, and it follows |

The abstract form (`omega3_geometric_shared`, `Shared.lean`) is stated for any `Hex B κ q`: proper 2-colouring, regular
of degree q+1, `egirth = 12`, connected, all distances ≤ 6. That is the incidence graph of any generalized hexagon of
order (q,q); H(q) is one instance. `geometric_of_shared` derives the all-pairs `Geometric` from `GeometricShared` by
the connectivity of the sharing graph (`copy_connected`, checked by `decide` on ZMod 5), and `omega3_geometric` reduces
to the normal form of Lemma 1.1 by an explicit graph homomorphism `Phi` with right inverse `Psi`. This is a valid way
to bound distance from below (a homomorphism does not increase distance).

### 5.2 Does the thesis wiring satisfy the hypotheses? Lemma 3.2

The wiring is not a hypothesis. It is built into `meets`/`omega`. `metPos` agrees with §1.2 of the note. For the
starved pair, `cstar` is the copy at position 3 of the first a-block, or position 0 of block 0 when all blocks are b.
This is the note's Lemma 3.2 with k = 0. `cstar_not_mem` (proved) says it is not in `CuK 0`, and `card_F0_le` (proved,
via `unique_star` by `decide` on all ZMod 5 data) says at most one copy of `CuK 0` per block reaches it by a barred
pass, so `|F0| ≤ α`. Lean only needs the upper bound.

Independent check that the graph really is the note's ΩH_q at small q: `research/lean-maxx/verify-omega3/build_omega.py`
rebuilds H(p) for p = 2, 3 **from the Lean definition of `HLine`** (Tits' equations, not any code of the note's), then
`omega` from `metPos`/`omegaRel` with the thesis labelling, and `bfs_hubs.c` runs BFS from every hub:

| q | pattern | ε₀ | far pairs (hub → vertex at distance ≥ 9) | note's thesis value 10N·3α·q⁵ |
|---:|---|---:|---:|---:|
| 2 | ab | 0 and 1 | 120,960 | 120,960 |
| 3 | aba | 0 and 1 | 7,960,680 (2,187 for every hub) | 7,960,680 |
| 3 | aab | 0 | 7,960,680 | |
| 3 | bbb | 0 | 10,909,080, eccentricity 10 | referee: all-b has eccentricity 10 |

The incidence graph passed its own checks (N = (q⁶−1)/(q−1), every line has q+1 points, diameter 6, sphere sizes
1, q+1, (q+1)q, …, q⁵). So the Lean wiring and graph reproduce the numbers the note and the referee report for the
thesis labelling. I have no access to the thesis itself; "this is Gómez's wiring" rests on §1.2 of the note and the
agreement with d12D8_table.md's numbers.

### 5.3 Weakenings and limits (none contradicts the statement of Theorem 3.3)

1. **Per-copy labelling model.** One bijection per copy serves both hub classes of a bar. This is the note's model.
   Labellings per (hub class, copy) with collineation transfers are outside it; the referee lists them as open (the
   counting method fails there). Not a weakening of Theorem 3.3, but anyone quoting "every labelling by collineations"
   should say "per copy".
2. **Only reading 2 and its dual** (`ε₀` global, the same colour for all unbarred classes in every copy). The note's
   Theorem 3.3 says exactly that. The note's Theorem 3.5 and the referee's duality reduction (any reading, any inner
   class per block, for q = 3^e) are **not formalised** (STATUS says so). For q ≠ 3^e this loses nothing, since other
   readings have no geometric labelling. For q = 9 (and 27, …) with inner classes chosen per block, the Lean files
   do not prove diameter ≥ 9; the note's Corollary 3.6 for (12,8) at q = 9 therefore rests on the referee's pen-and-paper
   reduction plus this Lean theorem, not on Lean alone.
3. **Explicit counts not exported.** The note's Theorem 3.3 also says every hub has at least q⁵ − αq⁴ − m₂q² vertices of
   c′ at distance ≥ 9 (3,712 at q = 8, …). Lean proves `omega3_far`/`omega3_ediam`: there exist a hub and a vertex at
   edist ≥ 9. The proof uses the bound for one arbitrary row t, but the exported statement is existence only. The
   Lean bound is also coarser (see 4), so the numbers would differ.
4. **Coarser internal constants** (do not change the statement): Lemma 3.1 is proved as `q⁴ + 2q²` for radius 4 (exact
   q⁴); `m2` counts families `|F1| + |F2| + |F3∖F0|` (overcounts the distinct centres); for q ≥ 10 the crude bound
   `m2 + |F0| ≤ 8α² + 6α`. For q = 8, 9 the exact counts of these families are checked for every pattern by
   `decide +kernel`. The margin is positive in all cases.
5. **q = 7 (Theorem 4.5) and Theorem 3.5 are not in the files**, as STATUS says. Theorem 3.3 is q ≥ 8 only.
6. Dualities: in reading 2 and its dual every labelling is colour-preserving, so `IsAut g` is automatically
   colour-preserving (`aut_col`); the "duality" clause of the task statement is vacuous there. It matters only for the
   mixed readings of item 2.

### 5.4 Satisfiability witness and toy model

The hypotheses are not vacuous.
* `omega3_hexagon_thesis` (in `Concrete.lean`) instantiates the geometric theorem with `μ c = 1` for all c: this is the
  thesis labelling, and it supplies the `hμ`/`GeometricShared` proofs for it.
* My `Check.lean` (all five theorems compile, axioms `[propext, Classical.choice, Quot.sound]`, see
  `Check.axioms.txt`):
  - `geoShared_of_collineations`: **every** family of colour-preserving automorphisms `g c` of the incidence graph is a
    `GeometricShared` labelling (transfer `g d * (g c)⁻¹`). So the hypotheses hold for as many labellings as H(q) has
    collineation families, not only the thesis one. `omega3_collineation_labelling` is the resulting corollary.
  - `gomez_alpha`: the headline theorem at α = ⌊(q+3)/2⌋ for an arbitrary finite field with q ≥ 8; the side
    conditions `0 < α`, `2α ≤ q+3` close by `omega`.
  - `q11`: `ZMod 11`, α = 7, all-a, ε₀ = 0, thesis labelling. `q8`: `GaloisField 2 3`, α = 5, all-b, ε₀ = 1. Both give
    `9 ≤ ediam`. These show the instances exist, including characteristic 2 (that was a risk: the older `Hexagon.Main`
    needs `NeZero 2`; the Omega3 files import `HexagonEven.Main`, which does not).
* There is no `Toy.lean` for Omega3 (Omega2 has one). In its place, the independent rebuild in §5.2 (q = 2, 3, which
  are not covered by the theorem) checks that the definitions of `omega` and `metPos` give the known graph.

### 5.5 Copies of Projection and Omega2

`sha256` of every file under `lean/BipartiteDD/LeanMaxx/Projection/` against `origin/claude/leanmaxx-projection-r0kehl`
(4 files) and under `.../Omega2/` against `origin/claude/omega2-theorem-2-formalization-61iulq` (10 files): **all 14 are
byte-identical.** (The Omega2 branch tip is e623fc9, the one the omega2 verifier accepted.)

## 6. Reproduce

    cd lean && export PATH=$HOME/.elan/bin:$PATH
    lake exe cache get
    for m in Balls Wiring Tables Graph Route Shape Main Geometric Shared Concrete Axioms; do lake build BipartiteDD.LeanMaxx.Omega3.$m; done
    lake env lean BipartiteDD/LeanMaxx/Omega3/Axioms.lean | diff - BipartiteDD/LeanMaxx/Omega3/Axioms.out.txt
    lake env lean ../research/lean-maxx/verify-omega3/Check.lean
    cd ../research/lean-maxx/verify-omega3
    gcc -O2 -o bfs_hubs bfs_hubs.c
    python3 build_omega.py 3 aba /tmp/om.edges && ./bfs_hubs /tmp/om.edges    # 7960680

Files in `research/lean-maxx/verify-omega3/`: `Check.lean`, `Check.axioms.txt`, `Axioms.regen.txt`, `build_omega.py`,
`bfs_hubs.c`, `omega_rebuild.log`.

Environment: elan from elan.lean-lang.org, Lean 4.34.1 (commit 5045d00), Mathlib cache from cache.mathlib.org.
