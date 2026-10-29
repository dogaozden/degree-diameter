# VERIFY: d5 (the diameter-5 theory of research/theorems/D5_QUADRANGLE.md, Lean files `lean/BipartiteDD/LeanMaxx/D5/`)

Job leanmaxx-verify-d5 (independent verifier, Sonnet). Verifier branch `claude/leanmaxx-verify-d5-f401e3`, made from
origin/master (ab2f6fb), with `origin/claude/d5-formalization-6yt0dm` (41ed251) merged. I did not use the worker's logs or
its `Axioms.out.txt` as evidence, and I changed no proof. My extra files are under `research/lean-maxx/verify-d5/` and are
not part of the Lean library.

Documents compared: the note `research/theorems/D5_QUADRANGLE.md` (branch `claude/d5-relax-searches-osr72a`, the version
with the (15,5) search numbers), the referee report `research/referee/d5-quadrangle.md` (branch
`claude/referee-d5-quadrangle-621u7o`), and the worker's `research/lean-maxx/STATUS-d5.md`.

## Verdict

**Accepted, with the limits in §5.** All 14 D5 files (13 modules and `Axioms.lean`) build from source with Lean 4.34.1 and Mathlib, with no sorry. The
regenerated axiom list is byte-identical to the committed one and shows only `propext`, `Classical.choice`, `Quot.sound`
for all 18 headline theorems. The statements say what the note says for Theorem A, Lemma 3.2, Theorems 3.5 and 3.6,
Theorem E, Theorem B (both directions), Theorem C and Proposition 7.2 (as the hypothesis (T') of Theorem 3.6). Corollary
10.3 is formalised only in a **weaker numerical form** (§5.1): the graph shape of the note, but with the non-friendly arcs
left whole (c = 0), the complete bipartite hub graph (Y0) and a counting partial ovoid. That form is still a theorem for
every odd prime power (§4), and I checked it against an independent computer rebuild at q = 5. What the Lean files do
**not** prove is any of the note's explicit lower bounds (11,552 and so on); they prove smaller ones.

## 1. Merge

`git merge origin/claude/d5-formalization-6yt0dm` into the branch at origin/master: **no conflicts**, a fast-forward.
`git diff --name-status origin/master HEAD` before my own files: 14 new Lean files in `LeanMaxx/D5/` (13 modules and
`Axioms.lean`) plus `Axioms.out.txt` and `research/lean-maxx/STATUS-d5.md`. Nothing existing is modified, so every
imported module (`GQ4.*`, `GQST.*`, `SingerC.*`, `Basic`) is byte-identical to master. The branch copies no earlier
verified files (no `Projection`, `Omega*`), so there was nothing to compare byte for byte.

## 2. Build, one module at a time, foreground-equivalent

Fresh container: no Lean. I installed elan, toolchain `leanprover/lean4:v4.34.1` (the repo's `lean-toolchain`), ran
`lake exe cache get` in `lean/` (8,908 Mathlib files), then `lake build <module>` one module per call, in dependency
order, from a script that waits for each (log: `verify-d5/build-order.log`; I did not end my turn while it ran).

| module | result | time |
|---|---|---|
| `GQST.Diam`, `GQ4.Count`, `GQST.Main`, `GQ4.Main` (imports from master) | OK | 8 s, 5 s, 13 s, 1 s |
| `SingerC.W3Main` (imports from master, builds all of SingerC) | OK | about 100 s |
| `D5.Reach` | OK | 3 s |
| `D5.Base` | OK | 3 s |
| `D5.Level` | OK | 3 s |
| `D5.ThmA` | OK | 3 s |
| `D5.Degree` | OK | 4 s |
| `D5.Assemble` | OK | 4 s |
| `D5.ThmE` | OK | 4 s |
| `D5.ThmB` | OK, linter warnings | 4 s |
| `D5.Layout7` | OK, linter warnings | 4 s |
| `D5.Family` | OK, linter warnings | 16 s |
| `D5.ThmC` | OK | 4 s |
| `D5.Lemma32` | OK | 4 s |
| `D5.ThmRelaxed` | OK, linter warnings | 3 s |
| `D5.Axioms` | OK | 13 s |

Every build exited 0. No log contains `sorry` or "declaration uses". The warnings are style linters only (unused
tactic, unused section variables, deprecated `if_pos`/`if_neg`/`push_neg`, `haveI` for a proposition).

## 3. Axioms

`lake env lean BipartiteDD/LeanMaxx/D5/Axioms.lean` (18 `#print axioms` lines: `repaired_of_empty`, `theoremA`,
`ediam_le_five`, `ediam_le_five_of_repaired`, `isBipartiteDegDiam`, `exists_graph`, `exists_graph_N`, `repaired_iff_E`,
`repaired_iff_partial`, `GQst.strong`, `repaired_of_partial`, `layout7`, `Setting.family_odd`, `repaired_of_local_dual`,
`repaired_iff_reach`, `reach_iff_E`, `reach_relaxed`, `GQst.base3`). Output saved as `verify-d5/Axioms.regen.txt`.
`diff` against the committed `lean/BipartiteDD/LeanMaxx/D5/Axioms.out.txt`: **identical**. All 18 lines read
`[propext, Classical.choice, Quot.sound]`. The lists are transitive, so the imported modules are covered.

## 4. Grep over `D5/*.lean`

Searched for: sorry, admit, axiom, native_decide, implemented_by, extern, unsafe, ofReduceBool, opaque, instance,
set_option, macro, elab, syntax, notation, attribute, partial, `@[`, `Lean.`, `run_cmd`, `initialize`, `decide +kernel`.

| term | hits | explanation |
|---|---|---|
| sorry, admit, axiom (as a command), native_decide, implemented_by, extern, unsafe, ofReduceBool, opaque, macro, elab, syntax, notation, attribute, partial, `@[`, `Lean.`, `run_cmd`, `initialize`, `decide +kernel` | 0 | |
| instance | 1 | `Layout7.lean:52`, `instance : DecidableRel T7`, a decidability instance for the tournament relation on `Fin 7`; used by `decide` and `Finset.filter`; it adds no axiom |
| set_option | 3 | `linter.unusedSectionVars false` in `Assemble`, `Degree`, `Family` (style linter only) |
| `#print axioms` | 18 | the lines of `Axioms.lean` |
| `open scoped Classical` | 4 files | classical decidability for `Finset.filter`; allowed, `Classical.choice` is on the list |

The `decide` calls are over `Fin 7` (`T7_*`, `arcV7_*`, `arcU7_*`) and use the kernel; `#print axioms layout7` shows no
`Lean.ofReduceBool`.

## 5. Statement fidelity

Throughout, the objects are the incidence graph `incGraph P L` of an abstract `GQst P L q q` (elements `P ⊕ L`, colour
`col`: points false, lines true), "distance ≤ n" is `Reach` (a walk of length ≤ n), and the level graph is
`Data.X = X_R^+` (vertices `((P ⊕ L) × ι) ⊕ (V ⊕ U)`), with `Data` carrying the tournament `T`, types `τ`, bijections
`M i j : (P ⊕ L) ≃ (P ⊕ L)` (only the restriction to `A_i` matters, and `Hyp.maps`/`Hyp.onto` force `A_i → B_j`), freed
sets `R i j`, hub slots `slotV`, `slotU`, hub graph `NS`. I read `Level.lean` and the definition of `Data.rel`: it has
level edges, matching edges `(x,i) ~ (M i j x, j)` for `T i j`, `col x = τ i`, `x ∉ R i j`, hub edges `slotV`/`slotU`
and the hub graph. That is Definitions 2.1 and 3.1.

| item in the note | in Lean | verdict |
|---|---|---|
| Definition 3.3 / (3.1): `d(u,a) + 1 + d(M a, v) ≤ 5` for some unfreed `a ∈ A_i` | `Data.Repaired` | matches |
| **Theorem A**: any tournament, typing, bijections: diameter ≤ 5, with the route form | `Hyp.theoremA` (V = U = Empty, `R = ∅`): `D.X.ediam ≤ 5`; route form `Hyp.repaired_of_empty` | matches. `Hyp` asks only `total` and `irrefl` for `T` (a regular tournament is not needed for the diameter), so it is slightly **more general** |
| **Lemma 3.2** (one matching edge) and Definition 3.3 on the two-level graph | `Hyp.repaired_iff_reach`: `Repaired i j ↔ ∀ u v, Reach (twoLevel D i j) (false,u) (true,v) 5` | matches; `twoLevel` is the two copies of `I` with the remaining matching edges |
| Lemma 3.4 | `Hyp.hub_level`, `Hyp.hub_hub` | matches |
| **Theorem 3.6** ((T') and (HG) ⇒ diameter ≤ 5) and **Theorem 3.5** ((T) and (HG)) | `Hyp.ediam_le_five`, `Hyp.ediam_le_five_of_repaired` (hub conditions stated as `Reach … 4` between same-colour hubs) | matches |
| Definition 3.1 degree and order; "hub graph degree ≤ q − r"; each slot taken at most once; Theorem 3.5's bound `n_b(q+1+r,5) ≥ (2r+1)·2N + K_A + K_B` | `Surg` (regular tournament `outdeg = r`, `card ι = 2r+1`, `arcV_inj`, `arcU_inj`, `hubV`, `hubU` as `deg + r ≤ q`), `Surg.degree_le`, `Hyp.colorable`, `Hyp.exists_graph` (graph on `Fin ((2r+1)(|P|+|L|)+|V|+|U|)`), `Hyp.exists_graph_N` (`2((q+1)(q²+1))` for `|P|+|L|`, needing the uniqueness half of the GQ axiom as the hypothesis `uniq`) | matches. Conclusion is `IsBipartiteDegDiam Y (q+1+r) 5` (2-colourable, every neighbour set of size ≤ q+1+r, `ediam ≤ 5`) |
| **Theorem E**: for `R ≠ ∅` repaired ⇔ (E2) ∧ (E3) | `Hyp.repaired_iff_E`, with `Data.E2` (`∀ x ∈ R, ∀ y` of colour `τ j`, `∃ a`, `Co x a ∧ a ∉ R ∧ Adj (M a) y`) and `Data.E3` (`∀ x ∈ R, ∀ b` of colour `!τ i`, `∃ a ∉ R, Adj b a ∧ Co (M x) (M a)`); hypotheses `R ⊆ A_i` and `R` nonempty | matches. `Co x a` is "x ≠ a with a common neighbour" = `a ∈ Γ₂(x)` |
| **Theorem B**, both directions: automorphic transition repaired ⇔ freed set has no two elements at distance 2 | `Hyp.repaired_iff_partial` (needs `Strong P L`, i.e. the uniqueness half (F4), derived from the axioms plus `uniq` by `GQst.strong`) and `Hyp.repaired_of_partial` (⇐ with base facts only); the automorphism is any `ψ : incGraph P L ≃g incGraph P L` agreeing with `M` on `A_i` | matches. "Partial ovoid/spread" is formalised as "no two distinct elements are `Co`", which is the same thing for points resp. lines. The iso `ψ` is any graph automorphism of `I`, so a collineation (identity) and a duality are both allowed |
| **Theorem C**: (H1) and (H3) ⇒ repaired | `Hyp.repaired_of_local_dual` | matches (no (H2), as the note says) |
| **Proposition 7.2** (hub rule) | `Hyp.reach_relaxed`: automorphic arc, `R` with every element having at most one `Co`-partner (R1), hub rule (R1h) for every ordered pair `(x, y)` of partners an `𝓐`-hub `g` with `slotU g j = M y` and `slotU g i` adjacent to `x`, `Base3`; conclusion every vertex of level i within 5 of every vertex of level j in `X_R^+` = (T') | matches, **in the referee's corrected form** (the hub exists and takes the slot; referee point 5). The conclusion is "≤ 5 for all pairs", which is (T'); the note's sharper "the bad pairs of Proposition 7.1 are at distance ≤ 4" is what the proof shows (`CL`, the hub route has length 4) but it is not exported, and Proposition 7.1 itself (the exact bad pairs) is not formalised, as STATUS says |
| **Corollary 10.3**, the 7-level layout HHHDHHD, `n_b(q+4,5) ≥ 14N + K_A + K_B` | `layout7` (shape) and `Setting.family_odd` (every odd prime power) | **weaker form, see §5.1** |

### 5.1 What is proved for Corollary 10.3, and how it differs from the note

`layout7` (any `GQst P L q q` with a bijection `P ≃ L`, a set `S` of lines no two meeting, a set `Z` of points no two
collinear, `1 ≤ K ≤ min(|S|,|Z|)`, `K + 3 ≤ q`) gives a bipartite graph on `7(|P|+|L|) + 2K` vertices, maximum degree
`q + 4`, diameter ≤ 5. I checked the layout against the note's Proposition 8.1: the rotational tournament
`i → i+1, i+2, i+3` on `Fin 7`; types `true` (A = lines, the dual reading of "H over Q(4,q)") on 0,1,2,4,5 and `false` on
3,6; the five `H→D` arcs (0→3, 1→3, 2→3, 4→6, 5→6) carry `S`, the five `D→H` arcs (3→4, 3→5, 6→0, 6→1, 6→2) carry `Z`,
the other eleven (ten `H→H`, one `D→D`: 3→6) have `M = Φ e` and nothing freed; hubs take one freed slot per level
(`arcV7`, `arcU7`, both checked by `decide` to be arcs of the tournament with the opposite type); the hub graph is
complete bipartite `K_{K,K}` of degree `K ≤ q − 3`. That is the layout of the note with these departures:

1. **c = 0.** The note's `c = 2` (two-point local dualities, Theorem C with Proposition 6.4, Corollary 6.2) on the
   non-friendly arcs is not used: the eleven non-friendly arcs have empty freed sets. Proposition 6.4 and Corollary 6.2 are
   not formalised. So the freed counts are `a = |S|`, `b = |Z|`, `c = 0` instead of `a = q²+1`, `b = 3q−1`, `c = 2`.
2. **Hub graph (Y0).** Complete bipartite, `K ≤ q − 3` per side, instead of the hub graphs of Lemma 9.1 with
   `K_B ≤ 6q`, `K_A ≤ 3q+3`. Lemma 9.1 is not formalised.
3. **Partial ovoid.** `Family.lean` takes a maximal partial ovoid of `W(3,q)` (size ≥ q−1 by a counting argument,
   `exists_partial_ovoid`, proved) instead of the explicit `3q−1` points of Lemma 1.3. Lemma 1.3 is not formalised.
4. **Generality in the other direction.** `layout7` holds for any quadrangle and any partial spread `S`, partial ovoid `Z`
   and bijection `P ≃ L` (the note fixes the ingredients). That is more general, not weaker.

`Setting.family_odd` instantiates `layout7` on the Singer model `W(3,q)` of `SingerC` (the regular spread of `q²+1`
pairwise disjoint lines): for `q = S.q` and `1 ≤ k ≤ q − 3` there is a bipartite graph on
`14(q+1)(q²+1) + 2k` vertices, maximum degree `q + 4`, diameter ≤ 5. The theorem quantifies over a `Setting K p`
(finite field `K` of odd characteristic `p`, `|K| = (p^e)^4`, a generator `g`). **"Every odd prime power q" is justified**:
my file `verify-d5/FamilyAllOdd.lean` proves, from `family_odd` and Mathlib alone (standard axioms only),

    theorem family_all_odd (p) [Fact p.Prime] (hodd : Odd p) (e) (he : 0 < e) (k) (hk1 : 1 ≤ k) (hkq : k + 3 ≤ p ^ e) :
      ∃ Y : SimpleGraph (Fin (14 * ((p^e + 1) * ((p^e)^2 + 1)) + k + k)), IsBipartiteDegDiam Y (p^e + 1 + 3) 5

by building `GaloisField p (4e)`, a generator of its unit group, and so a `Setting`. So the existence of the `Setting`
for each `q` is not an unstated assumption. For `q = 3` there is no `k` (`k + 3 ≤ 3`); `q ≥ 5` is needed.

**Arithmetic remark (mine, from the note's table values; I did not re-check the table).** `14N(q) + 2k` with
`N(q) = (q+1)(q²+1)` and `k ≤ q−3`: at q = 9 (Δ = 13) the formal family has 11,482 to 11,492 vertices, against the note's
2013 value 11,480 = 14·N(9) and the note's Corollary 10.3 value 11,552; at q = 11 (Δ = 15) it has 20,498 to 20,512,
against 20,496 and the note's 20,598; at q = 7 (Δ = 11) it has at most 5,608, below the 2013 value 5,850 (= 5·2N(8)).
So what is machine-checked is a family that is above the table by a few vertices in two of the cells, and below the note's
hand-proved values in all of them.

### 5.2 Against the referee's "What can be claimed"

| referee item | Lean status |
|---|---|
| 1. Theorem A, Lemma 3.2, Theorems 3.5/3.6, Theorem E, Theorem B both directions, Theorem C | **formalised**, as above |
| 1. Proposition 7.2 (with the hypothesis completed as in point 5) | **formalised as (T')** (`reach_relaxed`); Proposition 7.1 (exact bad pairs) is not |
| 1. Proposition 6.1, Corollary 6.2, Proposition 6.4, Propositions 8.1–8.3, Lemma 9.1, Lemmas 1.1, 1.3, 1.4, Proposition 2.2, the count of §13 | **not formalised** (Proposition 8.1's slot counts are only used implicitly through the explicit layout) |
| 2. Corollaries 10.1–10.4 with their numbers 4,044 … 20,598 | **not formalised**; only the weaker shape of 10.3 (§5.1) |
| 3. Computer-checked graphs (11,636; 20,713) | not in scope |
| 4. "Do not claim" list | Nothing in the Lean files or STATUS claims a record. STATUS says the orders are below Corollary 10.3 and below the lab's records |

The STATUS-d5.md table is accurate: every "done" row matches a theorem that builds, and its closing paragraph lists the
non-formalised items correctly (it also lists Lemma 9.1, Corollaries 10.1, 10.2, 10.4 among them). One wording point:
the row "order and degree … `n_b(q+1+r,5) ≥ (2r+1)·2N + K_A + K_B`" should be read as "a graph with that many vertices
exists" (`exists_graph_N`), which it is.

## 6. Independent computer rebuild of the seven-level graph

`verify-d5/rebuild_layout7.py` builds, **from the note's Definitions 2.1/3.1 and Proposition 8.1 only** (no Lean, no code
of the note's d5gq tools): `W(3,5)` from the symplectic trace form on `F_25²` (156 points, 156 totally isotropic lines,
GQ axiom checked by brute force), the regular spread from the `F_25`-lines (26 lines, a partition of the points), a greedy
maximal partial ovoid (16 to 18 points), a **random** bijection `P → L`, the seven-level graph with the layout of §5.1
(`S` = the spread on the `H→D` arcs, `Z` on the `D→H` arcs, `M = Φ e` on the eleven other arcs, `K` hubs of each kind,
complete bipartite hub graph), then bipartiteness, maximum degree and a BFS from every vertex.

| run | vertices | expected `14·156 + 2K` | max degree (q+4 = 9) | bipartite | diameter |
|---|---:|---:|---:|---|---:|
| K = 2, seed 1 | 2,188 | 2,188 | 9 | yes | **5** |
| K = 1, seed 7 | 2,186 | 2,186 | 9 | yes | **5** |
| K = 2, seed 99 | 2,188 | 2,188 | 9 | yes | **5** |
| negative control: K = 2, one point collinear with a freed point added to `Z` | 2,188 | 2,188 | 9 | yes | **6** |

(`verify-d5/rebuild_layout7.log`.) So the formal statement is true of the graph the note describes, at the smallest case
the family allows (q = 5, K ≤ 2), the order formula holds, and the partial-ovoid condition is necessary in this build,
as Theorem B says.

## 7. Limits of this verification

* The Lean statements are checked against the note and the referee; I did not re-verify the note's computer tables or
  the lab's records, and nothing here depends on them.
* `Hyp` bundles hypotheses (`base`, `irrefl`, `total`, `maps`, `onto`, `slotA`, `slotB`). They are satisfiable: `layout7`
  and `family_odd` instantiate them (`D7_hyp`), and the rebuild in §6 is the same data. Theorem B and `exists_graph_N` need
  the uniqueness half of the GQ axiom as a hypothesis (`uniq`); `GQst` records only the existence half. This is the
  standard axiom and it holds for every GQ; it is not a weakening of the note's statements.
* Proposition 7.2 is stated with Lean's (R1)/(R1h) as hypotheses on the data, as in the note. Whether the lab's relaxed
  sets satisfy them is a computer question (the note's Computer-checked 7.4), not covered here.
* Not formalised, so not verified: Proposition 6.1, Corollary 6.2, Proposition 6.4, Proposition 7.1, Lemma 7.3,
  Propositions 8.1–8.3 as counts, Lemma 9.1, Lemmas 1.1/1.3/1.4, Corollaries 10.1, 10.2, 10.4, §13, §14.
