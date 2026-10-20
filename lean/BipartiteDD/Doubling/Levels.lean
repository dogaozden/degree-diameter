import BipartiteDD.Doubling.Core
import BipartiteDD.Basic

/-! Group Doubling, part 3: Delorme's levelled doubling (Theorem 1 of `research/p4/hats/REPORT.md`),
bipartiteness and diameter.

Levels `A₀ ⊇ A₁ ⊇ …` are encoded by a height function `h : V → ℕ` with `A_i = {v | i < h v}`. A vertex of
level `k` (in `A_k ∖ A_{k+1}`) has height `k + 1` and gets `m ^ (k + 1)` versions, one for each string of
length `h v` over an `m`-letter alphabet; a vertex outside `A₀` has height `0` and one version (the empty
string). A string of length `a` is a function `Fin a → Fin m`.

Versions `x^s`, `y^t` are adjacent iff `x ~ y` in `G` and one string is a prefix of the other, i.e. `s`
and `t` agree on their common length (`Agree`).

For an infinite string `σ : ℕ → Fin m`, the versions `v^(σ restricted to h v)` form a *sheet*, and the
map `v ↦ v^(σ|h v)` is a graph homomorphism `G → levelled G m h`, so it does not increase distances. Two
versions whose strings agree lie in a common sheet. A vertex of height `0` lies in every sheet, which is
how a walk is moved from the sheet of `x^s` to the sheet of `y^t` in the other case. -/

namespace BipartiteDD.Doubling

open SimpleGraph
open scoped Classical

variable {V : Type*}

/-- Two strings agree on their common length: one is a prefix of the other. -/
def Agree {m a b : ℕ} (s : Fin a → Fin m) (t : Fin b → Fin m) : Prop :=
  ∀ (i : ℕ) (ha : i < a) (hb : i < b), s ⟨i, ha⟩ = t ⟨i, hb⟩

theorem Agree.symm {m a b : ℕ} {s : Fin a → Fin m} {t : Fin b → Fin m} (h : Agree s t) : Agree t s :=
  fun i hb ha => (h i ha hb).symm

/-- The versions: a vertex `v` of `G` with a string of length `h v` over `m` letters. -/
abbrev Ver (V : Type*) (m : ℕ) (h : V → ℕ) : Type _ := Σ v : V, (Fin (h v) → Fin m)

/-- Delorme's levelled doubling: `x^s ~ y^t` iff `x ~ y` in `G` and one string is a prefix of the other. -/
def levelled (G : SimpleGraph V) (m : ℕ) (h : V → ℕ) : SimpleGraph (Ver V m h) where
  Adj x y := G.Adj x.1 y.1 ∧ Agree x.2 y.2
  symm := ⟨fun _ _ hxy => ⟨hxy.1.symm, hxy.2.symm⟩⟩
  loopless := ⟨fun _ hx => G.irrefl hx.1⟩

variable {G : SimpleGraph V} {m : ℕ} {h : V → ℕ}

theorem levelled_adj {x y : Ver V m h} :
    (levelled G m h).Adj x y ↔ G.Adj x.1 y.1 ∧ Agree x.2 y.2 := Iff.rfl

/-- The number of versions is `∑ m ^ h v`. -/
theorem card_levelled [Fintype V] :
    Nat.card (Ver V m h) = ∑ v, m ^ h v := by
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_sigma]

/-! ### Bipartite -/

/-- Forgetting the string is a homomorphism `levelled G m h → G`. -/
def proj (G : SimpleGraph V) (m : ℕ) (h : V → ℕ) : levelled G m h →g G where
  toFun x := x.1
  map_rel' := fun hxy => hxy.1

/-- The levelled doubling of a bipartite graph is bipartite. -/
theorem levelled_colorable (hG : G.Colorable 2) : (levelled G m h).Colorable 2 :=
  Colorable.of_hom (proj G m h) hG

/-! ### Sheets and diameter -/

/-- The sheet of an infinite string `σ`: `v ↦ v^(σ restricted to h v)`. -/
def sheet (G : SimpleGraph V) (m : ℕ) (h : V → ℕ) (σ : ℕ → Fin m) : G →g levelled G m h where
  toFun v := ⟨v, fun i => σ i⟩
  map_rel' := fun huv => ⟨huv, fun _ _ _ => rfl⟩

/-- Every version lies in some sheet. -/
theorem exists_sheet (hm : 0 < m) (u : V) (s : Fin (h u) → Fin m) :
    ∃ σ : ℕ → Fin m, sheet G m h σ u = ⟨u, s⟩ := by
  refine ⟨fun i => if hi : i < h u then s ⟨i, hi⟩ else ⟨0, hm⟩, ?_⟩
  show (⟨u, _⟩ : Ver V m h) = ⟨u, s⟩
  congr 1
  funext i
  simp [i.2]

/-- Two versions with agreeing strings lie in a common sheet. -/
theorem exists_sheet_of_agree (hm : 0 < m) (u v : V) (s : Fin (h u) → Fin m) (t : Fin (h v) → Fin m)
    (hst : Agree s t) :
    ∃ σ : ℕ → Fin m, sheet G m h σ u = ⟨u, s⟩ ∧ sheet G m h σ v = ⟨v, t⟩ := by
  refine ⟨fun i => if ha : i < h u then s ⟨i, ha⟩ else if hb : i < h v then t ⟨i, hb⟩ else ⟨0, hm⟩,
    ?_, ?_⟩
  · show (⟨u, _⟩ : Ver V m h) = ⟨u, s⟩
    congr 1
    funext i
    simp [i.2]
  · show (⟨v, _⟩ : Ver V m h) = ⟨v, t⟩
    congr 1
    funext i
    by_cases ha : (i : ℕ) < h u
    · simp [ha, hst i ha i.2]
    · simp [ha, i.2]

/-- A vertex of height `0` has the same version in every sheet. -/
theorem sheet_of_height_zero {z : V} (hz : h z = 0) (σ τ : ℕ → Fin m) :
    sheet G m h σ z = sheet G m h τ z := by
  show (⟨z, _⟩ : Ver V m h) = ⟨z, _⟩
  congr 1
  funext i
  exfalso
  have := i.2
  omega

/-- Two versions are at distance at most `D` if `G` has diameter at most `D` and (c) holds for the set
`A₀ = {v | 0 < h v}` of vertices with more than one version. -/
theorem levelled_edist_le (hm : 0 < m) {D : ℕ} (hD : G.ediam ≤ D)
    (hc : CondC G {v | 0 < h v} D) (x y : Ver V m h) : (levelled G m h).edist x y ≤ D := by
  have hG : ∀ u v : V, G.edist u v ≤ D := fun u v => edist_le_ediam.trans hD
  obtain ⟨u, s⟩ := x
  obtain ⟨v, t⟩ := y
  by_cases hst : Agree s t
  · -- the strings are prefix-comparable: a common sheet
    obtain ⟨σ, hσu, hσv⟩ := exists_sheet_of_agree (G := G) hm u v s t hst
    have := edist_le_of_hom (sheet G m h σ) u v
    rw [hσu, hσv] at this
    exact this.trans (hG u v)
  · -- otherwise go through a vertex `z` of height `0`, which lies in every sheet
    obtain ⟨z, hz, hzD⟩ := exists_mid hc (hG u v)
    have hz0 : h z = 0 := by simpa using hz
    obtain ⟨σ, hσ⟩ := exists_sheet (G := G) hm u s
    obtain ⟨τ, hτ⟩ := exists_sheet (G := G) hm v t
    have h1 := edist_le_of_hom (sheet G m h σ) u z
    have h2 := edist_le_of_hom (sheet G m h τ) z v
    rw [hσ] at h1
    rw [hτ, sheet_of_height_zero hz0 τ σ] at h2
    calc (levelled G m h).edist ⟨u, s⟩ ⟨v, t⟩
        ≤ (levelled G m h).edist ⟨u, s⟩ (sheet G m h σ z) +
          (levelled G m h).edist (sheet G m h σ z) ⟨v, t⟩ := SimpleGraph.edist_triangle
      _ ≤ G.edist u z + G.edist z v := add_le_add h1 h2
      _ ≤ D := hzD

/-- The levelled doubling has diameter at most `D`. -/
theorem levelled_ediam (hm : 0 < m) {D : ℕ} (hD : G.ediam ≤ D) (hc : CondC G {v | 0 < h v} D) :
    (levelled G m h).ediam ≤ D :=
  ediam_le_iff.2 (levelled_edist_le hm hD hc)

end BipartiteDD.Doubling
