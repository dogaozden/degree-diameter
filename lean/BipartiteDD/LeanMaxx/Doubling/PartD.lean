import BipartiteDD.Doubling.Levels

/-! Lean-maxx, Doubling: Theorem 1.2(d) of `research/theorems/POLISHED.md` §1 (the converse of Delorme's
levelled doubling), for graphs.

Setting as in `BipartiteDD.Doubling.Levels`: `levelled G m h` is the levelled doubling with height `h`, and
`A₀ = {v | 0 < h v}` is the set of vertices with more than one version.

Statement (the note's (d)): if the doubled graph has diameter at most `D` and `m ≥ 2`, then for every two
vertices `x, y ∈ A₀` (possibly equal) there is `z ∉ A₀` with `d(x, z) + d(z, y) ≤ D`. This is the conclusion of
(C_D) for all pairs, with no assumption that `x` and `y` lie in one component of `G[A₀]`; `part_d_condC` gives
the `CondC` form, which is the same statement with the reachability hypothesis of `CondC` dropped.

Proof (the note's proof of (d)). Take the versions of `x` and `y` whose strings start with the letters `0`
and `1`. Along a walk between them, consecutive versions have prefix-comparable strings, and comparable
non-empty strings start with the same letter. So some version on the walk has the empty string, i.e. is a
vertex `z` with `h z = 0`. Splitting the walk at `z` and projecting it to `G` gives the bound.

The statement is for graphs. For an incidence structure `S` with incidence graph `Γ(S)`, the incidence graph
of `S^(m)_A` is `levelled Γ(S) m h`, so the graph statement gives (d) for incidence structures. -/

namespace BipartiteDD.LeanMaxx.Doubling

open BipartiteDD.Doubling
open SimpleGraph
open scoped Classical

variable {V : Type*}

/-- The version of `x` whose string is constantly `c` (of length `h x`). -/
def constVer {m : ℕ} (h : V → ℕ) (x : V) (c : Fin m) : Ver V m h :=
  ⟨x, fun _ => c⟩

/-- The first letter of a version, as a number. A version with the empty string has no first letter, and
we give it `0`; only versions with `0 < h` are used. -/
def firstLetter {m : ℕ} {h : V → ℕ} (x : Ver V m h) : ℕ :=
  if hx : 0 < h x.1 then (x.2 ⟨0, hx⟩).1 else 0

theorem firstLetter_constVer {m : ℕ} {h : V → ℕ} {x : V} (c : Fin m) (hx : 0 < h x) :
    firstLetter (constVer h x c) = c.1 := by
  simp [firstLetter, constVer, hx]

/-- Adjacent versions with positive heights have the same first letter: their strings are
prefix-comparable, so they agree at index `0`. -/
theorem firstLetter_eq_of_adj {m : ℕ} {G : SimpleGraph V} {h : V → ℕ} {x y : Ver V m h}
    (hxy : (levelled G m h).Adj x y) (hx : 0 < h x.1) (hy : 0 < h y.1) :
    firstLetter x = firstLetter y := by
  have hag : Agree x.2 y.2 := ((levelled_adj).1 hxy).2
  simp [firstLetter, hx, hy, hag 0 hx hy]

/-- Along a walk all of whose vertices have positive height, the first letter is constant. -/
theorem firstLetter_eq_of_walk {m : ℕ} {G : SimpleGraph V} {h : V → ℕ} {a b : Ver V m h}
    (p : (levelled G m h).Walk a b) (hp : ∀ z ∈ p.support, 0 < h z.1) :
    firstLetter a = firstLetter b := by
  induction p with
  | nil => rfl
  | @cons a c b hac p ih =>
    have ha : 0 < h a.1 := hp a (by simp)
    have hc : 0 < h c.1 := hp c (by simp)
    rw [firstLetter_eq_of_adj hac ha hc]
    exact ih fun z hz => hp z (by simp [hz])

/-- Theorem 1.2(d), in the form of the note: if the levelled doubling has diameter at most `D` and `m ≥ 2`,
then every two vertices of `A₀` (possibly equal) have a common vertex `z ∉ A₀` with
`d(x, z) + d(z, y) ≤ D`. -/
theorem part_d {G : SimpleGraph V} {m : ℕ} {h : V → ℕ} (hm : 2 ≤ m) {D : ℕ}
    (hD : (levelled G m h).ediam ≤ D) :
    ∀ x y : V, x ∈ {v | 0 < h v} → y ∈ {v | 0 < h v} →
      ∃ z, z ∉ {v | 0 < h v} ∧ G.edist x z + G.edist z y ≤ D := by
  intro x y hx hy
  have hx' : 0 < h x := hx
  have hy' : 0 < h y := hy
  -- the versions of `x` and `y` with first letters `0` and `1`
  have hXY : (levelled G m h).edist (constVer h x (⟨0, by omega⟩ : Fin m))
      (constVer h y (⟨1, by omega⟩ : Fin m)) ≤ D :=
    edist_le_ediam.trans hD
  have hne : firstLetter (constVer h x (⟨0, by omega⟩ : Fin m)) ≠
      firstLetter (constVer h y (⟨1, by omega⟩ : Fin m)) := by
    rw [firstLetter_constVer _ hx', firstLetter_constVer _ hy']
    simp
  set X := constVer h x (⟨0, by omega⟩ : Fin m) with hXdef
  set Y := constVer h y (⟨1, by omega⟩ : Fin m) with hYdef
  have hne' : (levelled G m h).edist X Y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top D) hXY
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top hne'
  -- some vertex of a shortest walk from `X` to `Y` has the empty string
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ p.support, h z.1 = 0 := by
    by_contra hall
    push Not at hall
    have hpos : ∀ z ∈ p.support, 0 < h z.1 := fun z hz => Nat.pos_of_ne_zero (hall z hz)
    exact hne (firstLetter_eq_of_walk p hpos)
  -- split the walk at `z`
  have hsplit : (levelled G m h).edist X z + (levelled G m h).edist z Y ≤ D := by
    have h1 : (levelled G m h).edist X z ≤ (p.takeUntil z hz).length := edist_le _
    have h2 : (levelled G m h).edist z Y ≤ (p.dropUntil z hz).length := edist_le _
    have h3 : (p.takeUntil z hz).length + (p.dropUntil z hz).length = p.length := by
      conv_rhs => rw [← p.take_spec hz]
      rw [Walk.length_append]
    calc (levelled G m h).edist X z + (levelled G m h).edist z Y
        ≤ ((p.takeUntil z hz).length : ℕ∞) + (p.dropUntil z hz).length := add_le_add h1 h2
      _ = (p.length : ℕ∞) := by exact_mod_cast h3
      _ = (levelled G m h).edist X Y := hp
      _ ≤ D := hXY
  -- project to `G`: the projection is a homomorphism, so it does not increase distances
  refine ⟨z.1, by simp [hz0], ?_⟩
  have hpx : G.edist x z.1 ≤ (levelled G m h).edist X z := edist_le_of_hom (proj G m h) X z
  have hpy : G.edist z.1 y ≤ (levelled G m h).edist z Y := edist_le_of_hom (proj G m h) z Y
  exact (add_le_add hpx hpy).trans hsplit

/-- Theorem 1.2(d) in the `CondC` form: the conclusion of (C_D) for `A₀ = {v | 0 < h v}`, for every pair
(the reachability hypothesis of `CondC` is not needed). -/
theorem part_d_condC {G : SimpleGraph V} {m : ℕ} {h : V → ℕ} (hm : 2 ≤ m) {D : ℕ}
    (hD : (levelled G m h).ediam ≤ D) : CondC G {v | 0 < h v} D :=
  fun x y hx hy _ => part_d hm hD x y hx hy

end BipartiteDD.LeanMaxx.Doubling
