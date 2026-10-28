import BipartiteDD.LeanMaxx.Omega3.Graph
import BipartiteDD.LeanMaxx.Omega2.Sphere

/-!
# Lemma 2.1: routes reach balls

A walk between two copy vertices of `ΩH_q` is a sequence of steps inside copies and passes (copy – hub –
copy). A *route* records, for such a walk, the passes `(bar, x)` (hub class colour and the copy entered)
and the number `a` of steps inside copies. `Route e c d fn a` says that, starting in copy `c` at a vertex
of colour `e`, the passes `fn` lead to copy `d`, using at most `a` steps inside copies. `ev mk c fn` is the
net transformation: the endpoint lies within `a` of `ev mk c fn y` where `y` is the starting vertex.

* `walk_route`: every walk `(c, y) → (d, z)` of length `n` gives a route with `a + 2 |fn| ≤ n` and a walk of
  length `≤ a` in `B` from `ev mk c fn y` to `z`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open Finset BipartiteDD.LeanMaxx.Omega2

variable {β : Type*} {α : ℕ}

/-- The transformation of a pass of class colour `bar` from copy `c` to copy `d`: it sends the mark of a row
in `c` to the mark of the same row in `d`. -/
def pT (mk : Bool → Copy α → Equiv.Perm β) (bar : Bool) (c d : Copy α) : Equiv.Perm β :=
  mk bar d * (mk bar c)⁻¹

theorem pT_apply (mk : Bool → Copy α → Equiv.Perm β) (bar : Bool) (c d : Copy α) (r : β) :
    pT mk bar c d (mk bar c r) = mk bar d r := by
  simp [pT]

/-- Routes: the passes are `(bar, x)` = a hub class of colour `bar` to copy `x`. At least one step inside
the current copy is allowed before each pass; `e` is the colour of the current vertex. -/
def Route (typ : Fin α → Bool) (ε₀ : ZMod 2) : ZMod 2 → Copy α → Copy α → List (Bool × Copy α) → ℕ → Prop
  | _, c, d, [], _ => c = d
  | e, c, d, (b, x) :: fn, a =>
      c ≠ x ∧ ∃ s, s ≤ a ∧ e + (s : ZMod 2) = hubcol ε₀ b ∧
        (∃ k, meets typ b k c = true ∧ meets typ b k x = true) ∧ Route typ ε₀ (hubcol ε₀ b) x d fn (a - s)

/-- The net transformation of the passes `fn` starting in copy `c`. -/
def ev (mk : Bool → Copy α → Equiv.Perm β) : Copy α → List (Bool × Copy α) → Equiv.Perm β
  | _, [] => 1
  | c, (b, x) :: fn => ev mk x fn * pT mk b c x

section

variable {typ : Fin α → Bool} {ε₀ : ZMod 2}

theorem route_step {e : ZMod 2} {c d : Copy α} {fn : List (Bool × Copy α)} {a : ℕ}
    (h : Route typ ε₀ (e + 1) c d fn a) : Route typ ε₀ e c d fn (a + 1) := by
  cases fn with
  | nil => exact h
  | cons p fn =>
    obtain ⟨b, x⟩ := p
    obtain ⟨hne, s, hs, hcol, hm, hr⟩ := h
    refine ⟨hne, s + 1, by omega, ?_, hm, ?_⟩
    · push_cast; rw [← hcol]; ring
    · rw [show a + 1 - (s + 1) = a - s by omega]; exact hr

theorem route_pass {e : ZMod 2} {c d x : Copy α} {fn : List (Bool × Copy α)} {a : ℕ} {b : Bool}
    (hne : c ≠ x) (he : e = hubcol ε₀ b) (hm : ∃ k, meets typ b k c = true ∧ meets typ b k x = true)
    (h : Route typ ε₀ (hubcol ε₀ b) x d fn a) : Route typ ε₀ e c d ((b, x) :: fn) a :=
  ⟨hne, 0, Nat.zero_le _, by simpa using he, hm, by simpa using h⟩

variable {B : SimpleGraph β} {κ : β → ZMod 2} {mk : Bool → Copy α → Equiv.Perm β}

theorem ev_mem (hmk : ∀ bar c, mk bar c ∈ autSub B κ) (c : Copy α) (fn : List (Bool × Copy α)) :
    ev mk c fn ∈ autSub B κ := by
  induction fn generalizing c with
  | nil => exact (autSub B κ).one_mem
  | cons p fn ih =>
    obtain ⟨b, x⟩ := p
    exact (autSub B κ).mul_mem (ih x) ((autSub B κ).mul_mem (hmk b x) ((autSub B κ).inv_mem (hmk b c)))

theorem ev_adj (hmk : ∀ bar c, mk bar c ∈ autSub B κ) (c : Copy α) (fn : List (Bool × Copy α)) {u v : β}
    (h : B.Adj u v) : B.Adj (ev mk c fn u) (ev mk c fn v) :=
  ((ev_mem hmk c fn).1 u v).2 h

/-- **Lemma 2.1 (routes), walk form.** A walk of length `n` between copy vertices `(c, y)` and `(d, z)` of
`ΩH_q` yields a route with `a + 2 |fn| ≤ n` and a `B`-walk of length `≤ a` from the transformed start. -/
theorem walk_route (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v) (hmkc : ∀ bar c u, κ (mk bar c u) = κ u)
    (hmk : ∀ bar c, mk bar c ∈ autSub B κ) :
    ∀ (n : ℕ) (c : Copy α) (y : β) (d : Copy α) (z : β)
      (w : (omega B κ typ ε₀ mk).Walk (Sum.inl (c, y)) (Sum.inl (d, z))), w.length = n →
      ∃ fn a, Route typ ε₀ (κ y) c d fn a ∧ a + 2 * fn.length ≤ n ∧
        ∃ wB : B.Walk (ev mk c fn y) z, wB.length ≤ a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c y d z w hw
  cases w with
  | nil =>
    have hn : n = 0 := by rw [← hw]; rfl
    subst hn
    exact ⟨[], 0, rfl, Nat.le_refl 0, ⟨SimpleGraph.Walk.nil, Nat.le_refl 0⟩⟩
  | @cons _ x _ h w' =>
    rcases x with ⟨c₂, y₂⟩ | hub
    · -- a step inside the copy
      rw [omega_adj_cc] at h
      obtain ⟨rfl, hadj⟩ := h
      obtain ⟨fn, a, hr, ha, wB, hwB⟩ := ih w'.length (by simp at hw; omega) _ _ _ _ w' rfl
      refine ⟨fn, a + 1, ?_, by simp at hw; omega, ?_⟩
      · refine route_step ?_
        have : κ y₂ = κ y + 1 := zmod2_eq_add_one (hκ _ _ hadj)
        rwa [← this]
      · exact ⟨SimpleGraph.Walk.cons (ev_adj hmk _ _ hadj) wB, by simp; omega⟩
    · -- a pass through the hub `hub`
      rw [omega_adj_ch] at h
      cases w' with
      | @cons _ x₂ _ h2 w'' =>
        rcases x₂ with ⟨c₂, y₂⟩ | hub₂
        · rw [omega_adj_hc] at h2
          have hlen : w''.length + 2 = n := by simp at hw; omega
          by_cases hcc : c = c₂
          · subst hcc
            have hy : y₂ = y := by rw [h2.2, h.2]
            subst hy
            obtain ⟨fn, a, hr, ha, wB, hwB⟩ := ih w''.length (by omega) _ _ _ _ w'' rfl
            exact ⟨fn, a, hr, by omega, wB, hwB⟩
          · obtain ⟨fn, a, hr, ha, wB, hwB⟩ := ih w''.length (by omega) _ _ _ _ w'' rfl
            have hcol : κ y = hubcol ε₀ hub.bar := by rw [h.2, hmkc]; exact hub.hr
            have hcol₂ : κ y₂ = hubcol ε₀ hub.bar := by rw [h2.2, hmkc]; exact hub.hr
            have hy₂ : pT mk hub.bar c c₂ y = y₂ := by
              rw [h.2, pT_apply, h2.2]
            refine ⟨(hub.bar, c₂) :: fn, a, ?_, by simp; omega, ?_⟩
            · refine route_pass hcc hcol ⟨hub.k, h.1, h2.1⟩ ?_
              rwa [hcol₂] at hr
            · have e : ev mk c ((hub.bar, c₂) :: fn) y = ev mk c₂ fn y₂ := by
                simp only [ev, Equiv.Perm.mul_apply, hy₂]
              rw [e]; exact ⟨wB, hwB⟩
        · exact absurd h2 not_omega_adj_hh

end

end BipartiteDD.LeanMaxx.Omega3
