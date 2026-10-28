import BipartiteDD.LeanAll.HexLocal

/-! # Voltage hub graphs

A bipartite hub graph with `K = b m` hubs of each kind: the voltage graph over `Z_m` of a base graph with `b`
vertices of each kind (`E`: edges `(x, y, v)`, `A_x ~ B_y` with voltage `v`). In the search graph on `2K` vertices,
hub `(t, x)` of the first kind is `2bt + x` and hub `(t, y)` of the second kind is `2bt + b + y`, so the shift
`t ↦ t - 1` moves every vertex `≥ 2b` below itself and the vertices `0 … 2b-1` represent all orbits (`Orbit2`).
`vhub`: from the local check and a diameter bound `7` of the search graph, every two hubs of the same kind are
within `6` in `hubGraph`, and the hub-graph degrees are at most `d`. -/

namespace BipartiteDD.LeanAll.VHub

open BipartiteDD BipartiteDD.HexagonD7 BipartiteDD.LeanAll.Orbit2 BipartiteDD.LeanAll.HexLocal
open SimpleGraph Finset
open scoped Classical

/-- `List.filterMap` by `List.rec`. -/
def fmapP {α β : Type} (f : α → Option β) (l : List α) : List β :=
  List.rec [] (fun a _ ih => match f a with | some y => y :: ih | none => ih) l

/-- Neighbours in the search graph. -/
def vnb (m b : ℕ) (E : List (ℕ × ℕ × ℕ)) (w : ℕ) : List ℕ :=
  cond (Nat.blt (w % (2 * b)) b)
    (fmapP (fun e => cond (Nat.beq e.1 (w % (2 * b)))
      (some (2 * b * ((w / (2 * b) + e.2.2) % m) + b + e.2.1)) none) E)
    (fmapP (fun e => cond (Nat.beq e.2.1 (w % (2 * b) - b))
      (some (2 * b * ((w / (2 * b) + m - e.2.2 % m) % m) + e.1)) none) E)

/-- The kind: `true` for the first kind. -/
def vcol (b w : ℕ) : Bool := Nat.blt (w % (2 * b)) b

/-- The shift and its inverse. -/
def vg (n b w : ℕ) : ℕ := (w + n - 2 * b) % n
def vh (n b w : ℕ) : ℕ := (w + 2 * b) % n

/-- Hub `v` of the first kind as a vertex. -/
def wV (b : ℕ) (v : ℕ) : ℕ := 2 * b * (v / b) + v % b
/-- Hub `u` of the second kind as a vertex. -/
def wU (b : ℕ) (u : ℕ) : ℕ := 2 * b * (u / b) + b + u % b

theorem div_mod_two {b r : ℕ} (hb : 0 < b) (X : ℕ) (hr : r < 2 * b) :
    (2 * b * X + r) / (2 * b) = X ∧ (2 * b * X + r) % (2 * b) = r := by
  constructor
  · rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
  · rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem wV_lt {b m : ℕ} (hb : 0 < b) {v : ℕ} (hv : v < b * m) : wV b v < 2 * (b * m) := by
  have h1 : v / b < m := by rw [Nat.div_lt_iff_lt_mul hb]; linarith
  have h2 := Nat.mod_lt v hb
  have h3 : v / b + 1 ≤ m := h1
  unfold wV
  nlinarith

theorem wU_lt {b m : ℕ} (hb : 0 < b) {u : ℕ} (hu : u < b * m) : wU b u < 2 * (b * m) := by
  have h1 : u / b < m := by rw [Nat.div_lt_iff_lt_mul hb]; linarith
  have h2 := Nat.mod_lt u hb
  have h3 : u / b + 1 ≤ m := h1
  unfold wU
  nlinarith

theorem wV_dm {b : ℕ} (hb : 0 < b) (v : ℕ) : wV b v / (2 * b) = v / b ∧ wV b v % (2 * b) = v % b :=
  div_mod_two hb _ (by have := Nat.mod_lt v hb; omega)

theorem wU_dm {b : ℕ} (hb : 0 < b) (u : ℕ) : wU b u / (2 * b) = u / b ∧ wU b u % (2 * b) = b + u % b := by
  have := div_mod_two hb (u / b) (r := b + u % b) (by have := Nat.mod_lt u hb; omega)
  unfold wU; rwa [Nat.add_assoc]

theorem vcol_wV {b : ℕ} (hb : 0 < b) (v : ℕ) : vcol b (wV b v) = true := by
  simp only [vcol, Nat.blt_eq]; rw [(wV_dm hb v).2]; exact Nat.mod_lt v hb

theorem vcol_wU {b : ℕ} (hb : 0 < b) (u : ℕ) : vcol b (wU b u) = false := by
  simp only [vcol]; rw [(wU_dm hb u).2]
  exact Bool.eq_false_iff.2 fun h => by have := ltOfBlt h; omega

theorem idx_lt {b m w : ℕ} (hb : 0 < b) (hw : w < 2 * (b * m)) (r : ℕ) (hr : r < b) :
    b * (w / (2 * b)) + r < b * m := by
  have h1 : w / (2 * b) < m := by rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
  have h3 : w / (2 * b) + 1 ≤ m := h1
  nlinarith

/-- A vertex of the search graph as a hub. -/
def toHubV (b m : ℕ) (hb : 0 < b) (w : Fin (2 * (b * m))) : Fin (b * m) ⊕ Fin (b * m) :=
  if h : w.val % (2 * b) < b then .inl ⟨b * (w.val / (2 * b)) + w.val % (2 * b), idx_lt hb w.isLt _ h⟩
  else .inr ⟨b * (w.val / (2 * b)) + (w.val % (2 * b) - b),
    idx_lt hb w.isLt _ (by have := Nat.mod_lt w.val (show 0 < 2 * b by omega); omega)⟩

theorem toHubV_wV {b m : ℕ} (hb : 0 < b) (v : Fin (b * m)) :
    toHubV b m hb ⟨wV b v.val, wV_lt hb v.isLt⟩ = .inl v := by
  obtain ⟨hd, hm⟩ := wV_dm hb v.val
  have hlt : v.val % b < b := Nat.mod_lt v.val hb
  unfold toHubV
  simp only [hm, hlt, dite_true, hd, Sum.inl.injEq]
  exact Fin.ext (Nat.div_add_mod v.val b)

theorem toHubV_wU {b m : ℕ} (hb : 0 < b) (u : Fin (b * m)) :
    toHubV b m hb ⟨wU b u.val, wU_lt hb u.isLt⟩ = .inr u := by
  obtain ⟨hd, hm⟩ := wU_dm hb u.val
  have hn : ¬ (b + u.val % b < b) := by omega
  unfold toHubV
  simp only [hm, hn, dite_false, hd, Sum.inr.injEq, Nat.add_sub_cancel_left]
  exact Fin.ext (Nat.div_add_mod u.val b)

/-- The hub graph: `v ~ u` when `u` is a neighbour of `v` in the search graph. -/
def vNS (m b : ℕ) (E : List (ℕ × ℕ × ℕ)) (v u : Fin (b * m)) : Prop := wU b u.val ∈ vnb m b E (wV b v.val)

variable {m b : ℕ} {E : List (ℕ × ℕ × ℕ)} {d : ℕ}

theorem vertex_cases (hb : 0 < b) (w : Fin (2 * (b * m))) :
    (∃ v : Fin (b * m), w.val = wV b v.val ∧ toHubV b m hb w = .inl v) ∨
      (∃ u : Fin (b * m), w.val = wU b u.val ∧ toHubV b m hb w = .inr u) := by
  have hm := Nat.mod_lt w.val (show 0 < 2 * b by omega)
  by_cases h : w.val % (2 * b) < b
  · left
    have hlt : b * (w.val / (2 * b)) + w.val % (2 * b) < b * m := idx_lt hb w.isLt _ h
    refine ⟨⟨_, hlt⟩, ?_, by simp [toHubV, h]⟩
    simp only [wV]
    rw [show (b * (w.val / (2 * b)) + w.val % (2 * b)) / b = w.val / (2 * b) by
          rw [Nat.mul_add_div hb, Nat.div_eq_of_lt h, Nat.add_zero],
        show (b * (w.val / (2 * b)) + w.val % (2 * b)) % b = w.val % (2 * b) by
          rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt h]
    exact (Nat.div_add_mod w.val (2 * b)).symm
  · right
    have hlt : b * (w.val / (2 * b)) + (w.val % (2 * b) - b) < b * m := idx_lt hb w.isLt _ (by omega)
    refine ⟨⟨_, hlt⟩, ?_, by simp [toHubV, h]⟩
    simp only [wU]
    rw [show (b * (w.val / (2 * b)) + (w.val % (2 * b) - b)) / b = w.val / (2 * b) by
          rw [Nat.mul_add_div hb, Nat.div_eq_of_lt (show w.val % (2 * b) - b < b by omega), Nat.add_zero],
        show (b * (w.val / (2 * b)) + (w.val % (2 * b) - b)) % b = w.val % (2 * b) - b by
          rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (show w.val % (2 * b) - b < b by omega)]
    have := Nat.div_add_mod w.val (2 * b)
    omega

/-- The search graph maps into the hub graph. -/
def vHom (hb : 0 < b) (hL : LocalSpec d (2 * (b * m)) (vnb m b E) (vcol b)) :
    graphF (2 * (b * m)) (vnb m b E) →g hubGraph (vNS m b E) where
  toFun := toHubV b m hb
  map_rel' := by
    intro a c hac
    have hc := (adj_iff hL).1 hac
    have hcol := hL.col a.val a.isLt c.val hc
    rcases vertex_cases hb a with ⟨v, hav, ha⟩ | ⟨u, hau, ha⟩ <;>
      rcases vertex_cases hb c with ⟨v', hcv, hc'⟩ | ⟨u', hcu, hc'⟩ <;> rw [ha, hc']
    · rw [hav, hcv, vcol_wV hb, vcol_wV hb] at hcol; exact absurd rfl hcol
    · refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl ?_⟩
      show wU b u'.val ∈ vnb m b E (wV b v.val)
      rw [← hav, ← hcu]; exact hc
    · refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr ?_⟩
      show wU b u.val ∈ vnb m b E (wV b v'.val)
      rw [← hau, ← hcv]; exact hL.symm a.val a.isLt c.val hc
    · rw [hau, hcu, vcol_wU hb, vcol_wU hb] at hcol; exact absurd rfl hcol

theorem reach_of (hb : 0 < b) (hL : LocalSpec d (2 * (b * m)) (vnb m b E) (vcol b))
    (hD : (graphF (2 * (b * m)) (vnb m b E)).ediam ≤ 7) (a c : Fin (2 * (b * m)))
    (hac : vcol b a.val = vcol b c.val) :
    Reach (hubGraph (vNS m b E)) (toHubV b m hb a) (toHubV b m hb c) 6 := by
  have he : (graphF (2 * (b * m)) (vnb m b E)).edist a c ≤ 7 :=
    le_trans (SimpleGraph.edist_le_ediam) hD
  have hne : (graphF (2 * (b * m)) (vnb m b E)).edist a c ≠ ⊤ :=
    ne_top_of_le_ne_top (by exact ENat.natCast_ne_top 7) he
  obtain ⟨w, hw⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
  have h7 : w.length ≤ 7 := by
    have : (w.length : ℕ∞) ≤ 7 := hw ▸ he
    exact_mod_cast this
  have hev : Even w.length := (col_walk hL w).1 hac
  have h6 : Reach (graphF (2 * (b * m)) (vnb m b E)) a c 6 := ⟨w, by rcases hev with ⟨k, hk⟩; omega⟩
  exact Reach.map (vHom hb hL) h6

/-- **Voltage hub graphs.** -/
theorem vhub (hb : 0 < b) (hL : LocalSpec d (2 * (b * m)) (vnb m b E) (vcol b))
    (hD : (graphF (2 * (b * m)) (vnb m b E)).ediam ≤ 7) :
    (∀ v v' : Fin (b * m), Reach (hubGraph (vNS m b E)) (.inl v) (.inl v') 6) ∧
    (∀ u u' : Fin (b * m), Reach (hubGraph (vNS m b E)) (.inr u) (.inr u') 6) ∧
    (∀ v, (univ.filter (vNS m b E v)).card ≤ d) ∧ (∀ u, (univ.filter (fun v => vNS m b E v u)).card ≤ d) := by
  refine ⟨fun v v' => ?_, fun u u' => ?_, fun v => ?_, fun u => ?_⟩
  · have := reach_of hb hL hD ⟨wV b v.val, wV_lt hb v.isLt⟩ ⟨wV b v'.val, wV_lt hb v'.isLt⟩
      (by rw [vcol_wV hb, vcol_wV hb])
    rwa [toHubV_wV, toHubV_wV] at this
  · have := reach_of hb hL hD ⟨wU b u.val, wU_lt hb u.isLt⟩ ⟨wU b u'.val, wU_lt hb u'.isLt⟩
      (by rw [vcol_wU hb, vcol_wU hb])
    rwa [toHubV_wU, toHubV_wU] at this
  · have hinj : ∀ u u' : Fin (b * m), wU b u.val = wU b u'.val → u = u' := by
      intro u u' h
      have h1 := toHubV_wU hb u
      have h2 := toHubV_wU hb u'
      have : (⟨wU b u.val, wU_lt hb u.isLt⟩ : Fin (2 * (b * m))) = ⟨wU b u'.val, wU_lt hb u'.isLt⟩ := Fin.ext h
      rw [this, h2] at h1
      exact (Sum.inr_injective h1).symm
    refine le_trans ?_ ((List.toFinset_card_le _).trans (hL.deg _ (wV_lt hb v.isLt)))
    refine Finset.card_le_card_of_injOn (fun u => wU b u.val) (fun u hu => ?_) (fun u _ u' _ h => hinj u u' h)
    have hu' : vNS m b E v u := (Finset.mem_filter.1 hu).2
    exact List.mem_toFinset.2 hu'
  · have hinj : ∀ v v' : Fin (b * m), wV b v.val = wV b v'.val → v = v' := by
      intro v v' h
      have h1 := toHubV_wV hb v
      have h2 := toHubV_wV hb v'
      have : (⟨wV b v.val, wV_lt hb v.isLt⟩ : Fin (2 * (b * m))) = ⟨wV b v'.val, wV_lt hb v'.isLt⟩ := Fin.ext h
      rw [this, h2] at h1
      exact (Sum.inl_injective h1).symm
    refine le_trans ?_ ((List.toFinset_card_le _).trans (hL.deg _ (wU_lt hb u.isLt)))
    refine Finset.card_le_card_of_injOn (fun v => wV b v.val) (fun v hv => ?_) (fun v _ v' _ h => hinj v v' h)
    have hv' : vNS m b E v u := (Finset.mem_filter.1 hv).2
    exact List.mem_toFinset.2 (hL.symm _ (wV_lt hb v.isLt) _ hv')

end BipartiteDD.LeanAll.VHub
