# VERIFY: omega45b (Lemma 4.3 and Theorem 4.5 of research/theorems/OMEGA_REPAIR.md for H(7), Lean files `lean/BipartiteDD/LeanMaxx/Omega45b/`)

Job leanmaxx-verify-d5, part (B) (independent verifier, Sonnet). Verifier branch `claude/leanmaxx-verify-d5-omega45b`,
made from origin/master (ab2f6fb), with `origin/claude/thm-omega45-q7-formalize-unw57v` (eac168e) merged. I did not use
the worker's logs or its `Axioms.out.txt` as evidence, and I changed no proof. My extra files are under
`research/lean-maxx/verify-omega45b/` and are not part of the Lean library.

Documents compared: the note `research/theorems/OMEGA_REPAIR.md` (branch `claude/thm-omega-repair-m4luls`, §4), and the
worker's `research/lean-maxx/STATUS-omega45b.md`. Earlier verifications of the copied files:
`research/lean-maxx/VERIFY-omega2.md` and `VERIFY-omega3.md` (branches `claude/leanmaxx-verify-omega2-lms0i1`,
`claude/leanmaxx-verify-omega3-jas79g`).

## Verdict

**Accepted as what STATUS says it is: Lemma 4.3 for H(7) is proved, and Theorem 4.5 for H(7) is proved from Lemma 4.4
as an explicit hypothesis. Theorem 4.5 for H(7) is not proved unconditionally in Lean.**

* All 43 modules build (Projection, Omega2, Omega3, Omega45 and Omega45b), each with `lake build <module>` one at a time,
  no sorry. The five regenerated axiom lists are byte-identical to the committed ones; every headline theorem depends on
  `propext`, `Classical.choice`, `Quot.sound` only (one auxiliary lemma on `propext`, `Quot.sound`).
* Lemma 4.4 occurs **only as a hypothesis**: the plain definition `Lemma44 : Prop` (`PerpQuadric.lean:21`), the first
  argument of `omega45_H7_geometric` and of `perpBound_of_lemma44`. It is not an axiom, not a `sorry`, and no theorem
  concludes it. Its statement is the note's (§4 below).
* **Lemma 4.3 is proved in a weaker numerical form than the note's** (fewer than 4 close pairs instead of fewer than 6;
  §3.1). That form is what the double count of Theorem 4.5 needs, and the note itself says so. It is not "Lemma 4.3 as
  stated" and the STATUS file says this correctly.
* Files copied from earlier branches (`Projection`, `Omega2`, `Omega3`, `Omega45`) are byte-identical to their source
  branches (§1).
* Two housekeeping points for the worker: `STATUS-omega45b.md` still contains the unreplaced line `CHARSUM_PLACEHOLDER`
  (between "Why Lemma 4.4 is not here" and "Files"), and `Omega45b/Diag7.lean` (zero counts of diagonal forms in seven
  variables) is imported by nothing. It builds, uses only `decide +kernel`, and proves nothing the headline needs.

## 1. Merge and byte-identity of copies

`git merge origin/claude/thm-omega45-q7-formalize-unw57v` into the branch at origin/master: **no conflicts**.
`git diff --name-status origin/master HEAD`: 54 files, all additions (A): 48 files under `LeanMaxx/` (`Omega2` 10,
`Omega3` 12, `Omega45` 10, `Omega45b` 12, `Projection` 4: 43 Lean modules and 5 `Axioms.out.txt`) and six notes under `research/lean-maxx/`. Nothing existing is
modified.

`git diff <branch> HEAD -- lean/BipartiteDD/LeanMaxx/<dir>` is empty for every pair below, with the file count on the
source branch equal to the count here:

| directory | compared with | files | result |
|---|---|---:|---|
| `Omega2` | `claude/thm-omega3-formalization-r197t8` | 10 | identical |
| `Omega2` | `claude/omega2-theorem-2-formalization-61iulq` | 10 | identical |
| `Omega2` | `claude/leanmaxx-verify-omega2-lms0i1` (the verified version) | 10 | identical |
| `Omega3` | `claude/thm-omega3-formalization-r197t8` | 12 | identical |
| `Omega3` | `claude/leanmaxx-verify-omega3-jas79g` (the verified version) | 12 | identical |
| `Projection` | `claude/thm-omega3-formalization-r197t8` | 4 | identical |
| `Omega45` | `claude/thm-omega45-q7-formalize-0ih1sy` | 10 | identical |
| `Omega2`, `Omega3`, `Projection` | `claude/thm-omega45-q7-formalize-0ih1sy` | 10, 12, 4 | identical |

The branch contains no lean-all module copies; the imports from `Hexagon.*`, `HexagonEven.*`, `Doubling.Hat` come from
master and are untouched.

## 2. Build, one module at a time, foreground-equivalent

Fresh container: no Lean. I installed elan, toolchain `leanprover/lean4:v4.34.1` (the repo's `lean-toolchain`), ran
`lake exe cache get` in `lean/` (8,908 Mathlib files), then `lake build <module>` once per module, in dependency order,
from a script that waits for each (log: `verify-omega45b/build-order.log`; I did not end my turn while it ran). 4 cores,
15 GB.

| group | modules (seconds each) | result |
|---|---|---|
| `Projection` | `Walk` 4, `Main` 2, `Axioms` 3 | OK |
| `Omega2` | `Sphere` 8, `Count` 14, `Trace` 4, `Reach` 14, `Main` 14, `Polygon` 84, `HexQ` 13, `Toy` 13, `Axioms` 12 | OK |
| `Omega3` | `Balls` 6, `Wiring` 15, **`Tables` 235**, `Graph` 21, `Route` 14, `Shape` 15, `Main` 15, `Geometric` 14, `Shared` 14, `Concrete` 37, `Axioms` 12 | OK |
| `Omega45` | `Exact` 6, `Cover` 13, **`Tab7` 237**, `Q7` 15, `Flip` 13, `Geometric7` 13, `Concrete7` 12, `Dual7` 12, `Axioms` 12 | OK |
| `Omega45b` | `Defs` 13, `Zcount` 16, `QuadCount` 14, `Bridge` 13, `Points` 14, `Bonf` 23, `Assemble` 17, `Main` 12, `PerpQuadric` 13, `Diag7` 55, `Axioms` 11 | OK |

Every build exited 0 (43 of 43). No log contains `sorry`, "declaration uses" or an error. No build was killed on
15 GB (`Tab7` and `Tables` are the slow ones, about four minutes). The warnings are style linters only.

## 3. Axioms

`lake env lean BipartiteDD/LeanMaxx/<dir>/Axioms.lean` for `Projection`, `Omega2`, `Omega3`, `Omega45`, `Omega45b`
(4 + 15 + 17 + 20 + 16 = 72 output lines, 64 `depends on axioms` entries). Outputs saved as
`verify-omega45b/Axioms.regen.<dir>.txt`; `diff` against the committed `Axioms.out.txt` of each directory: **identical in
all five**. Every entry reads `[propext, Classical.choice, Quot.sound]` (some wrapped over three lines) except
`Omega2.exists_trace`, which depends on `[propext, Quot.sound]` only. The Omega45b list covers `wzeros5`, `wzeros4`,
`card_perpZeros_two`, `card_perpZeros_three_le`, `dist_inl_le_four_iff`, `dist_inl_eq_six_iff`, `perp_of_dependent`,
`card_pts_mul`, `bonf3`, `union_bound`, `pair_overlap_pts`, `triple_pts_le`, `bonferroni_of_hex`,
`omega45_H7_of_perpBound`, `perpBound_of_lemma44`, `omega45_H7_geometric`. My own `Check.lean` re-prints axioms for
`bonferroni_of_hex`, `omega45_H7_geometric`, `omega45_H7_of_perpBound`, `perpBound_of_lemma44`: standard three.

## 4. Grep over the new files

Searched `Omega45b/*.lean`, `Omega45/*.lean` (and, for completeness, `Omega3`, `Omega2`, `Projection`) for: sorry, admit,
axiom, native_decide, implemented_by, extern, unsafe, ofReduceBool, opaque, instance, set_option, macro, elab, syntax,
notation, attribute, partial, run_cmd, initialize, `decide +kernel`, `decide +native`, `@[`, `Lean.`, `#eval`, `#exit`,
noncomputable.

| term | hits | explanation |
|---|---|---|
| sorry, admit, axiom (as a command; the word occurs in comments), native_decide, implemented_by, extern, unsafe, ofReduceBool, opaque, macro, elab, syntax, notation, attribute, partial, run_cmd, initialize, `decide +native`, `Lean.`, `#eval`, `#exit` | 0 in all five directories | |
| instance | `Omega45b/Defs.lean:18` `instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩`; `Diag7.lean:17` a `Decidable` instance for `good7`; `QuadCount.lean:24,26` `local instance NeZero (2 : F7)` and `Invertible (2 : F7)`, proved by `decide` | true facts about `ZMod 7`; no axiom |
| set_option | `linter.unusedSectionVars false` and `linter.style.longLine false` (style only); `maxHeartbeats 1000000 in` at `Bonf.lean:79`; `maxRecDepth 100000` in `Tab7.lean` and `Omega3/Tables.lean` | resource limits for kernel evaluation; no axiom |
| `decide +kernel` | `Bonf.lean:126`, `Diag7.lean:24`, `Zcount.lean:119,126`; `Tab7.lean` (about 40 uses); `Omega3/Tables.lean` (11) | kernel evaluation of closed decidable statements (square-class tables over `F7`, the 2¹⁵-case `special_le`, wiring tables). `#print axioms` shows no `Lean.ofReduceBool` anywhere |
| `@[` | `Omega3/Graph.lean:28,29` `@[simp]` on two `rfl` lemmas | |
| noncomputable | `Omega3`, `Omega45`, `Omega2` definitions over `Finset.filter` with classical decidability | |

## 5. Statement fidelity

### 5.1 Lemma 4.3 (`bonferroni_of_hex`, `Assemble.lean:187`)

    theorem bonferroni_of_hex (H : Hex G7 klass 7) : Bonferroni G7 klass 0 4 140

with (`Omega45/Q7.lean`)

    Bonferroni B κ ε₀ k m := ∀ t Y, κ t = ε₀ → |Y| = 5 → (∀ y ∈ Y, κ y = ε₀ ∧ y ≠ t) →
        2·|{y ∈ Y : dist t y ≤ 4}| + |{(y,y') ∈ Y×Y : y ≠ y', dist y y' ≤ 4}| < 2k →
        |⋃_{y ∈ Y} ballOpp B t y 4| + m·7² < 7⁵

Here `ballOpp B t y 4` is the set of vertices at distance 6 from `t` and ≤ 4 from `y`. So for six distinct points
`t, y₁..y₅` with fewer than `k` of the 15 pairs at distance ≤ 4 (perpendicular, by the bridge `dist_inl_le_four_iff`), the
radius-4 balls around the `yᵢ` cover so few points opposite `t` that `m = 140` radius-2 balls (≤ 49 points each) cannot
cover the rest (`|opp(t)| ≥ 7⁵`). `G7 = incGraph (hexInc (F := ZMod 7))` is the incidence graph of the split Cayley
hexagon H(7) (Tits' six equations, `Hexagon/Defs.lean`; `Hex G7 klass 7` is supplied by `hex_hexagon`).

Differences from the note's Lemma 4.3:

1. **k = 4, not k = 6.** The note: for the 8 non-degenerate types plus general position the bound holds, and "every one
   of the other 9 types forces at least 6 of the 15 pairs to be perpendicular" (353 labelled configurations, computer
   enumeration `degen.py`). Equivalently: fewer than 6 close pairs ⇒ far vertex. Lean proves: fewer than **4** close pairs ⇒
   far vertex. The note's statement implies Lean's (`bonferroni_mono`; my `Check.lean` has the one-line example); Lean's
   does not imply the note's. The note's Theorem 4.5 proof says four forced pairs per point suffice (4N = 78,432 > 62,160),
   and the double count in `Omega45/Q7.lean` (`omega45_of_hyps`) uses 4: `8 ≤ 2A + B` at every row, summed against
   `7⁵ ≤ |opp|`, versus `(2·5 + 20)·4144 = 124,320 < 8·16,807 = 134,456`.
2. **No type enumeration.** The note analyses 17 structure types; Lean avoids them. With fewer than 4 close pairs it uses
   `special_le` (a 2¹⁵-case kernel check: at most one aligned pair or at most one collinear triple, not both), the
   inclusion–exclusion bound `bonf3` for five sets (level 3), pair overlaps ≥ 336 and triple overlaps ≤ 64 (Lemma 4.1:
   `pair_overlap`, `triple_overlap`), giving a union of at most 9,621 points, and `9621 + 140·49 < 7⁵`.
3. Lemma 4.1's counts, as Lean theorems: `card_perpZeros_two` (for independent singular `y, y'` the space `⟨y,y'⟩^⊥` has
   exactly 2401 zeros of `Qf`), `card_perpZeros_three_le` (for independent singular `y, y', y''`, at most 385 zeros, so ≤ 64
   points). The note's Lemma 4.1 says ≥ q³ − q = 336 for pair overlaps and ≤ (q+1)² = 64 for triples; same numbers.

STATUS-omega45b says exactly this (its "Differences from the note" item 1 and the "k = 4" paragraph), so STATUS does not
overclaim.

### 5.2 Lemma 4.4 (`Lemma44`, `PerpQuadric.lean:21`) is only a hypothesis

    def Lemma44 : Prop :=
      ∀ h : autSub G7 klass, (∀ p : SPt F7, h (inl p) ≠ inl p) →
        Nat.card {s : SPt F7 // ∃ p : SPt F7, h (inl s) = inl p ∧ Bf s.rep p.rep = 0} ≤ 4144

* It is a `def … : Prop`, used as an argument. `grep -n Lemma44` shows it in `PerpQuadric.lean` only. `#print axioms`
  of `omega45_H7_geometric` contains no extra axiom; the theorem's type begins `Lemma44 → …`.
* Against the note's Lemma 4.4 ("q odd with 3 | q−1, h ∈ G₂(q) fixes no point of H(q); then Perp(h) = {s : h(s) ⊥ s} has at
  most (q⁵−1)/(q−1) + q^{3.5} + q³ + (q−2)q^{1.5} points: at most 4,144 of the 19,608 points when q = 7"): the bound
  4144 is right (2801 + 907.5 + 343 + 92.6 = 4144.1); "fixes no point" is `∀ p, h (inl p) ≠ inl p`; "h(s) ⊥ s" is
  `Bf s.rep (h s).rep = 0`, which equals distance ≤ 4 by `dist_inl_le_four_iff` (proved in `Bridge.lean`); the class of
  `h` is all colour-preserving automorphisms of `G7` (`autSub`), that is all collineations of H(7). The note takes
  `h ∈ G₂(7)`; these coincide because the collineation group of H(7) is G₂(7) (a classification result not in Lean, and
  not needed to read the Lean statement). If the collineation group were larger the Lean hypothesis would be stronger, but
  it is not. `perpBound_of_lemma44` then turns it into `PerpBound G7 klass 0 4144` for `Omega45/Q7.lean` (the set of rows at
  distance ≤ 4 from their image). I read the proof: it maps the `Finset` of `PerpSet` to the subtype by the bridge, no gap.
* It is a faithful, not a weakened, rendering. It is **not proved**; STATUS says so and explains why (G₂ classification,
  Gauss sums, eigenvalue structure).

### 5.3 Theorem 4.5 (`omega45_H7_geometric`, `PerpQuadric.lean:57`)

    theorem omega45_H7_geometric (hL : Lemma44) {α : ℕ} (hα : 0 < α) (h2 : 2*α ≤ 7+3)
        (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm (SPt F7 ⊕ HLine F7))
        (hμ : ∀ c u, klass (μ c u) = klass u) (hgeo : Geometric G7 klass μ) :
        9 ≤ (omega G7 klass typ ε₀ (labMk μ)).ediam

| item in the note | in Lean | verdict |
|---|---|---|
| q = 7, the hexagon H(7) | `G7`, `F7 = ZMod 7`; `Hex G7 klass 7` from `hex_hexagon` (all finite fields, via Omega2/Omega3 as verified) | matches |
| every block pattern (Gómez: α = 5 blocks of five copies, α = ⌊(q+3)/2⌋) | `typ : Fin α → Bool` arbitrary, `0 < α`, `2α ≤ 10` (so α ≤ 5) | matches and is more general (any α from 1 to 5) |
| reading 2 and its point/line dual | `ε₀ : ZMod 2` arbitrary, so both readings; `omega45_H7_of_perpBound` takes `hε : ε₀ = 0 ∨ ε₀ + 1 = 0`, discharged by `decide` over `ZMod 2` | matches. The dual reading is reduced to the first by the bar-exchange isomorphism `Flip.lean` (`metPos_flip`, a finite check), instead of the note's computer-checked "starved pairs with X barred" |
| the starved pair (Computer-checked 4.0) | replaced by Lemma 3.2's `cstar` and the kernel tables of `Tab7.lean` (`|F0| = α`, `|D2| ≤ 140` for q = 7, every pattern) | different proof route, same use; built here |
| geometric labelling, collineations chosen per copy | `Geometric G7 klass μ`: for each colour `ε` and copies `c, d` there is a graph automorphism `g` with `μ d r = g (μ c r)` for rows `r` of colour `ε`; `hμ` colour-preserving | matches (see below) |
| Lemma 4.2 (coincidences) | `omega45_lemma42`, unconditional, in `Omega45/Q7.lean` | proved |
| Lemma 4.3 | `bonferroni_of_hex` | proved, k = 4 (§5.1) |
| Lemma 4.4 | hypothesis `hL : Lemma44` | **assumed** |
| the double count, 15 collineations `gᵢ`, `gᵢ⁻¹gⱼ`, Σ|Perp| ≥ 6N against 15·4144 | `omega45_of_hyps` (`Q7.lean`), with k = 4 | proved |
| conclusion: diameter ≥ 9 | `9 ≤ ediam` in `ℕ∞` (`ediam = ⊤` also satisfies it) | matches |

On `Geometric` versus the note's "geometric labelling": the Omega3 headline uses `GeometricShared` (transfers along shared
hub classes) and derives `Geometric` from it by connectivity of the sharing graph (`geometric_of_shared`, Omega3 as
verified). `omega45_H7_geometric` is stated with the all-pairs `Geometric`; my `Check.lean` composes the two to obtain the
`GeometricShared` form with the same hypothesis `Lemma44` only (`omega45_H7_geometric_shared_check`, standard axioms). The
statement is not vacuous: the identity labelling satisfies `hμ` and `Geometric` (checked in `Check.lean`).

So the logical content of Lean is: for H(7), **Lemma44 ⟹ Theorem 4.5**. Theorem 4.5 for H(7) is not established in Lean
until Lemma 4.4 is.

## 6. Independent numeric checks (Python, numpy; no Lean code)

Both scripts use only the quadric `Q = x₀x₄ + x₁x₅ + x₂x₆ − x₃²` and Tits' six equations as in `Hexagon/Defs.lean`.

**`verify-omega45b/check_lemma43_numeric.py`** (log `check_lemma43_numeric.log`, three seeds): all 19,608 singular points
of Q(6,7). (a) For random singular `y, y'` (perpendicular and not) the space `⟨y,y'⟩^⊥` has exactly 2401 zeros of Q;
triples give 301, 343 or 385 zeros, never more (Lean: ≤ 385). (b) Over random independent `(t, y, y')` the pair overlap
`|C_y ∩ C_y'|`, with `C_y = {x singular : B(t,x) ≠ 0, B(y,x) = 0}`, has minimum **336** (Lean/note: ≥ 336); the triple
perp-intersections have at most **64** points (Lean/note: ≤ 64). (c) Over about 560 random and structured configurations per
seed (aligned `yᵢ` on a totally singular line through `t`, `yᵢ` on a line not through `t`) with fewer than 4 of the 15 pairs
perpendicular, the largest union `|⋃Cᵢ|` is 9,291 to 9,298,
below Lean's bound 9,621 and the threshold `7⁵ − 140·49 = 9,947` (by number of close pairs 0, 1, 2, 3 the largest unions, seed 1, are 9,068; 9,084; 9,085; 9,291). This agrees with Lemma 4.3 in the k = 4 form; it is a
sampling check, not a proof of the worst case.

**`verify-omega45b/check_lemma44_sampling.py`** (log `check_lemma44_sampling.log`, four runs): samples the **hypothesis**
`Lemma44`. Collineations are random products of long root elations `x ↦ x + b(x,u)v − b(x,v)u` with `(u,v)` a hexagon line
(Q = 0, B = 0, Tits). Checks: each elation maps sampled hexagon-line pairs to hexagon-line pairs (20 of 20); elations with a
singular axis that is not a hexagon line do not (20 of 20 fail, negative control); each point has 56 partners on its 8 lines.
The long root groups generate G₂(7) (7 is not a power of 3). Of 700 random products of 3, 8 and 20 elations, 389 are
fixed-point-free (a single elation fixes 400 points, so those 200 samples are not fixed-point-free); for them `|Perp(h)|` has minimum **2,752** and maximum **2,850**, far below 4,144, and the same two
extremes as the note ("the true values are 2,752 and 2,850"). So the hypothesis is consistent with these samples. This does
not prove Lemma 4.4.

## 7. Limits of this verification

* Theorem 4.5 at H(7) is conditional on `Lemma44`. I did not try to prove or disprove it. The sampling in §6 supports it,
  and the note's argument (character sum, ranks, eigenvalue structure of G₂) was refereed on paper by the note's referee;
  I did not re-read that proof.
* I checked the statements of `Hexagon/Defs.lean` (Q, B, Tits, `IsHPair`, `SPt`, `HLine`) against the note's H(q) only as
  far as the numbers above use them; the earlier VERIFY-omega3 rebuilt H(p) for p = 2, 3 from this definition.
* The wiring `omega` and `Geometric` are those of Omega3 and Omega45, which are byte-identical to the verified Omega3/Omega2
  and to `claude/thm-omega45-q7-formalize-0ih1sy`. The Omega45 modules (`Exact`, `Cover`, `Tab7`, `Q7`, `Flip`,
  `Geometric7`, `Concrete7`, `Dual7`) were built and their axioms regenerated here; I read `Q7.lean`, `Flip.lean`,
  `Dual7.lean`, `Geometric7.lean`, `Concrete7.lean` and `Omega45b/Main.lean`, `PerpQuadric.lean`, `Defs.lean`, `Diag7.lean`
  in full and the statements of the other Omega45b files; I did not re-read every proof line of the counting files
  (`Zcount`, `QuadCount`, `Bonf`, `Assemble`, `Points`, `Bridge`), whose results are the numbers checked in §6.
