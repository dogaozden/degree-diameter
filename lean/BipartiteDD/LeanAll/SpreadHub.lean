import BipartiteDD.LeanAll.RouteHub
import BipartiteDD.LeanAll.HexGlobal

/-! # Freed spreads with cluster-assisted hubs (the (12,7) construction, research/squads/cells/d12D7.md)

`Spread.exists_graph` with `RouteHub.HHyp`: same-side hubs within `6` in the whole graph (`exists_graph`). For the
cell the distances come from an auxiliary graph `A` (`Orbit2.graphF`) on hubs, freed points, spread lines and their
dual images at every level, with a map `ι` into the graph (`auxHom`: every edge of `A` checked against the tables),
and a search in `A` from one hub of each kind, spread to all hubs by automorphisms of `A` that keep the hubs and their
kinds (`hub_edist`); only the hubs are required in the final masks (`fin_of`). `main` assembles it with
`HexGlobal.TabOK`. -/

namespace BipartiteDD.LeanAll.SpreadHub

open SimpleGraph Finset BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.Typed BipartiteDD.LeanAll.Spread
open BipartiteDD.LeanAll.RouteHub BipartiteDD.LeanAll.Orbit2 BipartiteDD.Fast
open scoped Classical

set_option linter.unusedSectionVars false

/-! ## The theorem with hub distances in the graph -/

section Gen

variable {P L : Type*} {inc : P → L → Prop} {F : Set P}
variable {V U : Type*} [Fintype P] [Fintype L] [Fintype V] [Fintype U] {q j : ℕ}

/-- The graph of a freed spread with a duality. -/
abbrev XS (inc : P → L → Prop) (j : ℕ) (F : Set P) (φP : P ≃ L) (φL : L ≃ P) (slotV : V → ZMod (2 * j + 1) → P)
    (slotU : U → ZMod (2 * j + 1) → P) (NS : V → U → Prop) : SimpleGraph (Typed.Vtx P L V U j) :=
  X inc j (fun _ => false) (fun _ _ => dualE φP φL) (fun _ _ => freedE (L := L) F) (fun v i => .inl (slotV v i))
    (fun u i => .inr (φP (slotU u i))) NS

/-- **Freed spread with a duality, hubs through the graph.** -/
theorem exists_graph (hB : Base inc) (hS : SpreadLike inc F) {φP : P ≃ L} {φL : L ≃ P}
    (hφ : ∀ p l, inc p l ↔ inc (φL l) (φP p))
    (hdeg : ∀ x : P ⊕ L, (univ.filter ((Hexagon.incGraph inc).Adj x)).card ≤ q + 1)
    (slotV : V → ZMod (2 * j + 1) → P) (slotU : U → ZMod (2 * j + 1) → P) (NS : V → U → Prop)
    (hFV : ∀ v i, slotV v i ∈ F) (hFU : ∀ u i, slotU u i ∈ F)
    (hSV : ∀ i (p : P), (univ.filter (fun v => slotV v i = p)).card ≤ j)
    (hSU : ∀ i (p : P), (univ.filter (fun u => slotU u i = p)).card ≤ j)
    (hubV : ∀ v v', Reach (XS inc j F φP φL slotV slotU NS) (.inr (.inl v)) (.inr (.inl v')) 6)
    (hubU : ∀ u u', Reach (XS inc j F φP φL slotV slotU NS) (.inr (.inr u)) (.inr (.inr u')) 6)
    (hNV : ∀ v, (univ.filter (NS v)).card ≤ q - j) (hNU : ∀ u, (univ.filter (fun v => NS v u)).card ≤ q - j)
    (hjq : j ≤ q) :
    ∃ G : SimpleGraph (Fin ((2 * j + 1) * (Fintype.card P + Fintype.card L) + Fintype.card V + Fintype.card U)),
      IsBipartiteDegDiam G (q + 1 + j) 7 := by
  set δ := dualE φP φL
  have H : HHyp inc j (fun _ => false) (fun _ _ => δ) (fun _ _ => freedE F) (fun v i => .inl (slotV v i))
      (fun u i => .inr (φP (slotU u i))) NS := by
    refine ⟨hB, ?_, ?_, ?_, ?_, fun _ _ => rfl, fun _ _ => rfl, hubV, hubU⟩
    · intro i k _ _ x hx
      rcases x with p | l
      · rfl
      · simp [colE] at hx
    · intro i k _ _ y hy
      rcases y with p | l
      · simp [colE] at hy
      · show colE (δ.symm (.inr l)) = false
        have : δ.symm (.inr l) = .inl (φP.symm l) := by
          rw [Equiv.symm_apply_eq]; simp [δ]
        rw [this]; rfl
    · intro i k _ _ x ⟨p, _, he⟩
      rw [he]; rfl
    · intro i k _ _ a b
      exact route_dual hB hS hφ a b
  have hj : ∀ (x : P ⊕ L), x ∈ freedE (L := L) F →
      ((Finset.Icc 1 j).filter (fun k => x ∈ freedE (L := L) F)).card = j := by
    intro x hx
    rw [Finset.filter_true_of_mem (fun _ _ => hx)]; simp
  refine H.exists_graph hdeg (fun (i : ZMod (2 * j + 1)) (x : P ⊕ L) => ?_)
    (fun (i : ZMod (2 * j + 1)) (x : P ⊕ L) => ?_) hNV hNU hjq
  · by_cases hx : ∃ p, x = .inl p ∧ p ∈ F
    · obtain ⟨p, rfl, hp⟩ := hx
      rw [hj _ ⟨p, hp, rfl⟩]
      refine le_trans (Finset.card_le_card fun v hv => ?_) (hSV i p)
      simp only [mem_filter, mem_univ, true_and] at hv ⊢
      exact Sum.inl_injective hv
    · have : univ.filter (fun v => (Sum.inl (slotV v i) : P ⊕ L) = x) = ∅ := by
        ext v
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hv
        exact hx ⟨slotV v i, hv.symm, hFV v i⟩
      rw [this]; simp
  · by_cases hx : ∃ p, x = .inr (φP p) ∧ p ∈ F
    · obtain ⟨p, rfl, hp⟩ := hx
      have hδ : ∀ k : ℕ, δ.symm (.inr (φP p)) = .inl p := fun _ => by
        rw [Equiv.symm_apply_eq]; simp [δ]
      have : ((Finset.Icc 1 j).filter (fun k : ℕ => δ.symm (.inr (φP p)) ∈ freedE (L := L) F)).card = j := by
        rw [Finset.filter_true_of_mem (fun k _ => by rw [hδ k]; exact ⟨p, hp, rfl⟩)]; simp
      refine le_trans ?_ (le_of_eq this.symm)
      refine le_trans (Finset.card_le_card fun u hu => ?_) (hSU i p)
      simp only [mem_filter, mem_univ, true_and] at hu ⊢
      exact φP.injective (Sum.inr_injective hu)
    · have : univ.filter (fun u => (Sum.inr (φP (slotU u i)) : P ⊕ L) = x) = ∅ := by
        ext u
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hu
        exact hx ⟨slotU u i, hu.symm, hFU u i⟩
      rw [this]; simp

end Gen

/-! ## Hub distances in an auxiliary graph -/

section Aux

variable {n : ℕ}

/-- Vertices `< H` of the same colour within `D`, from sources `< m` and automorphisms that keep `[0, H)` and the
colour. -/
theorem hub_edist {d D m H : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    (gens : List ((ℕ → ℕ) × (ℕ → ℕ))) (hP : ∀ g ∈ gens, PermSpec n nb g.1 g.2)
    (hH : ∀ g ∈ gens, ∀ v < H, g.1 v < H ∧ c (g.1 v) = c v)
    (hO : ∀ v, m ≤ v → v < H → ∃ g ∈ gens, g.1 v < v)
    (hB : ∀ s (hs : s < n), s < m → ∀ w : Fin n, w.val < H → c w.val = c s → (graphF n nb).edist w ⟨s, hs⟩ ≤ D) :
    ∀ v w : Fin n, v.val < H → w.val < H → c v.val = c w.val → (graphF n nb).edist v w ≤ D := by
  suffices h : ∀ i, ∀ v w : Fin n, v.val = i → v.val < H → w.val < H → c v.val = c w.val →
      (graphF n nb).edist v w ≤ D from fun v w => h v.val v w rfl
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro v w hvi hv hw hc
    by_cases hm : i < m
    · have e : v = ⟨i, hvi ▸ v.isLt⟩ := Fin.ext hvi
      rw [SimpleGraph.edist_comm, e]
      exact hB i _ hm w hw (by rw [← hc, hvi])
    · obtain ⟨g, hg, hlt⟩ := hO i (by omega) (hvi ▸ hv)
      have hPσ := hP g hg
      have h1 := hH g hg v.val hv
      have h2 := hH g hg w.val hw
      calc (graphF n nb).edist v w ≤ (graphF n nb).edist (permF hPσ v) (permF hPσ w) := edist_le_perm hL hPσ v w
        _ ≤ D := ih (g.1 i) (by rw [← hvi] at hlt ⊢; exact hlt) (permF hPσ v) (permF hPσ w)
            (by simp [permF, hvi]) (by simpa [permF] using h1.1) (by simpa [permF] using h2.1)
            (by simp only [permF]; rw [h1.2, h2.2, hc])

/-- The final check on `lo' ≤ v < lo' + len`: bit `j` wherever the colour is that of source `lo + j`. -/
noncomputable def finOK (K : ℕ) (T : Fast.Tree ℕ) (c : ℕ → Bool) (lo k lo' len : ℕ) : Bool :=
  allR (fun v => allR (fun j => (c v != c (lo + j)) || Nat.testBit (look T K v) j) 0 k) lo' len

/-- Masks of every radius as data, each step checked: a set bit is a distance bound. -/
theorem edist_of_levels {K D lo k d : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    (hK : n ≤ 2 ^ K) (Lv : ℕ → Fast.Tree ℕ) (h0 : Lv 0 = Tree.gen (initMask lo k) 0 K)
    (hs : ∀ r < D, ∀ v < n, look (Lv (r + 1)) K v = foldOr (fun u => look (Lv r) K u) (nb v) (look (Lv r) K v))
    (v : Fin n) (j : ℕ) (hj : (look (Lv D) K v.val).testBit j = true) :
    ∃ hjn : lo + j < n, (graphF n nb).edist v ⟨lo + j, hjn⟩ ≤ D := by
  have hlev : ∀ r ≤ D, ∀ v < n, look (Lv r) K v = ballM nb lo k r v := by
    intro r
    induction r with
    | zero =>
      intro _ v hv
      rw [h0, look_gen_lt _ K v (by omega)]
      rfl
    | succ r ih =>
      intro hr v hv
      rw [hs r (by omega) v hv, foldOr_eq, ih (by omega) v hv]
      simp only [ballM]
      exact foldl_or_congr _ _ _ (fun u hu => ih (by omega) u (hL.lt v hv u hu)) _
  rw [hlev D le_rfl v.val v.isLt] at hj
  exact edist_of_testBit hL lo k D v j hj

/-- The final check gives the source bounds of `hub_edist`. -/
theorem fin_of {K D k d H : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c)
    (hK : n ≤ 2 ^ K) (Lv : ℕ → Fast.Tree ℕ) (h0 : Lv 0 = Tree.gen (initMask 0 k) 0 K)
    (hs : ∀ r < D, ∀ v < n, look (Lv (r + 1)) K v = foldOr (fun u => look (Lv r) K u) (nb v) (look (Lv r) K v))
    (hf : ∀ v < H, ∀ j < k, ((c v != c (0 + j)) || Nat.testBit (look (Lv D) K v) j) = true) :
    ∀ s (hs : s < n), s < k → ∀ w : Fin n, w.val < H → c w.val = c s → (graphF n nb).edist w ⟨s, hs⟩ ≤ D := by
  intro s hsn hsk w hw hc
  have := hf w.val hw s hsk
  rw [Nat.zero_add, hc] at this
  simp only [bne_self_eq_false, Bool.false_or] at this
  obtain ⟨_, he⟩ := edist_of_levels hL hK Lv h0 hs w s this
  have e : (⟨0 + s, by omega⟩ : Fin n) = ⟨s, hsn⟩ := Fin.ext (Nat.zero_add s)
  rwa [e] at he

theorem finOK_spec {K : ℕ} {T : Fast.Tree ℕ} {c : ℕ → Bool} {lo k lo' len : ℕ} (h : finOK K T c lo k lo' len = true) :
    ∀ v, lo' ≤ v → v < lo' + len → ∀ j < k, ((c v != c (lo + j)) || Nat.testBit (look T K v) j) = true := by
  intro v h1 h2 j hj
  have := allR_spec h v h1 h2
  exact allR_spec this j (Nat.zero_le _) (by omega)

/-- A distance bound gives a walk. -/
theorem reach_of_edist {W : Type*} {G : SimpleGraph W} {a b : W} {D : ℕ} (h : G.edist a b ≤ D) : Reach G a b D := by
  have hne : G.edist a b ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top D) h
  obtain ⟨w, hw⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
  refine ⟨w, ?_⟩
  have : (w.length : ℕ∞) ≤ D := hw ▸ h
  exact_mod_cast this

end Aux

/-! ## The cell: tables, owners, the auxiliary graph -/

section Cell

open BipartiteDD.LeanAll.HexGen BipartiteDD.LeanAll.HexGlobal BipartiteDD.LeanAll.HexLocal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Owners of hub `v`: freed-list indices `< KF`, and `v` in the inverse list of each. -/
def ownOK (KF J : ℕ) (o : ℕ → ℕ → ℕ) (inv : ℕ → List ℕ) (v : ℕ) : Bool :=
  allR (fun i => Nat.blt (o v i) KF && (inv (i * KF + o v i)).any (Nat.beq v)) 0 J

/-- An inverse owner list has at most `j` hubs. -/
def invOK (j : ℕ) (invV invU : ℕ → List ℕ) (e : ℕ) : Bool := Nat.ble (lenP (invV e)) j && Nat.ble (lenP (invU e)) j

/-- The hub graph at line-side hub `v` (`hubL`) and its inverse (`hubR`). -/
def hubOK (K d : ℕ) (hubL hubR : ℕ → List ℕ) (v : ℕ) : Bool :=
  Nat.ble (lenP (hubL v)) d && Nat.ble (lenP (hubR v)) d && allP (fun u => Nat.blt u K && (hubR u).any (Nat.beq v)) (hubL v)

/-- An edge of the auxiliary graph. Kinds `kA`: `0` line-side hub, `1` point-side hub, `2` point, `3` line; `aA` the
hub number or the table index, `lA` the level. -/
def auxE (N K J : ℕ) (dP fpt : ℕ → ℕ) (ents : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)) (oV oU : ℕ → ℕ → ℕ)
    (hubL : ℕ → List ℕ) (kA aA lA : ℕ → ℕ) (u w : ℕ) : Bool :=
  (Nat.beq (kA u) 0 && Nat.beq (kA w) 2 && Nat.blt (aA u) K && Nat.blt (lA w) J &&
    Nat.beq (fpt (oV (aA u) (lA w))) (aA w)) ||
  (Nat.beq (kA u) 2 && Nat.beq (kA w) 0 && Nat.blt (aA w) K && Nat.blt (lA u) J &&
    Nat.beq (fpt (oV (aA w) (lA u))) (aA u)) ||
  (Nat.beq (kA u) 1 && Nat.beq (kA w) 3 && Nat.blt (aA u) K && Nat.blt (lA w) J &&
    Nat.beq (dP (fpt (oU (aA u) (lA w)))) (aA w)) ||
  (Nat.beq (kA u) 3 && Nat.beq (kA w) 1 && Nat.blt (aA w) K && Nat.blt (lA u) J &&
    Nat.beq (dP (fpt (oU (aA w) (lA u)))) (aA u)) ||
  (Nat.beq (kA u) 2 && Nat.beq (kA w) 3 && Nat.beq (lA u) (lA w) && Nat.blt (aA w) N &&
    (ents (aA w)).any (fun t => Nat.beq t.1 (aA u))) ||
  (Nat.beq (kA u) 3 && Nat.beq (kA w) 2 && Nat.beq (lA u) (lA w) && Nat.blt (aA u) N &&
    (ents (aA u)).any (fun t => Nat.beq t.1 (aA w))) ||
  (Nat.beq (kA u) 0 && Nat.beq (kA w) 1 && Nat.blt (aA u) K && Nat.blt (aA w) K &&
    (hubL (aA u)).any (Nat.beq (aA w))) ||
  (Nat.beq (kA u) 1 && Nat.beq (kA w) 0 && Nat.blt (aA u) K && Nat.blt (aA w) K &&
    (hubL (aA w)).any (Nat.beq (aA u)))

/-- The colour of the auxiliary graph: line-side hubs and lines. -/
def auxC (kA : ℕ → ℕ) (a : ℕ) : Bool := Nat.beq (kA a) 0 || Nat.beq (kA a) 3

variable {C : Coder F} {q N : ℕ} {pc la lb dP dPi dL dLi sl : ℕ → ℕ} {fP fL : ℕ → Bool}
  {ents : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)}

/-- The slots: hub `v` sits at the freed point `fpt (o v i)` in level `i`. -/
noncomputable def slotOf (C : Coder F) (pc fpt : ℕ → ℕ) (j K : ℕ) (o : ℕ → ℕ → ℕ) (v : Fin K)
    (i : ZMod (2 * j + 1)) : SPt F :=
  P_ C pc (fpt (o v.val i.val))

/-- The hub graph. -/
def NSof (K : ℕ) (hubL : ℕ → List ℕ) (v u : Fin K) : Prop := (hubL v.val).any (Nat.beq u.val) = true

/-- The map of the auxiliary graph into the graph. -/
noncomputable def iota (C : Coder F) (pc la lb : ℕ → ℕ) (j K : ℕ) (hK : 0 < K) (kA aA lA : ℕ → ℕ) (a : ℕ) :
    Typed.Vtx (SPt F) (HLine F) (Fin K) (Fin K) j :=
  if kA a = 0 then .inr (.inl ⟨aA a % K, Nat.mod_lt _ hK⟩)
  else if kA a = 1 then .inr (.inr ⟨aA a % K, Nat.mod_lt _ hK⟩)
  else if kA a = 2 then .inl (.inl (P_ C pc (aA a)), (lA a : ZMod (2 * j + 1)))
  else .inl (.inr (L_ C la lb (aA a)), (lA a : ZMod (2 * j + 1)))

theorem zval {j l : ℕ} (h : l < 2 * j + 1) : ((l : ZMod (2 * j + 1)) : ZMod (2 * j + 1)).val = l := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

variable (T : TabOK C q N pc la lb dP dPi dL dLi sl fP fL ents)
include T

theorem tφP {p : ℕ} (hp : p < N) : T.φP (P_ C pc p) = L_ C la lb (dP p) := by
  have := T.φP_ptE ⟨p, hp⟩
  rwa [T.ptE_apply] at this

theorem tinc {l : ℕ} (hl : l < N) {t : ℕ × ℕ × ℕ × ℕ × ℕ} (ht : t ∈ ents l) :
    hexInc (P_ C pc t.1) (L_ C la lb l) :=
  HexGen.inc_of_lin (T.ptB (T.ent hl t ht).1) (T.lnB hl) (T.ent hl t ht).2.1

/-- **The auxiliary graph maps into the graph.** -/
theorem auxHom {j K KF nA dA : ℕ} (hK : 0 < K) {fpt : ℕ → ℕ} (hfpt : ∀ f < KF, fpt f < N)
    {oV oU : ℕ → ℕ → ℕ} (hoV : ∀ v < K, ∀ i < 2 * j + 1, oV v i < KF) (hoU : ∀ v < K, ∀ i < 2 * j + 1, oU v i < KF)
    {hubL : ℕ → List ℕ} {kA aA lA : ℕ → ℕ} {nbA : ℕ → List ℕ}
    (hLA : LocalSpec dA nA nbA (auxC kA))
    (hE : ∀ u < nA, ∀ w ∈ nbA u, auxE N K (2 * j + 1) dP fpt ents oV oU hubL kA aA lA u w = true)
    (a b : Fin nA) (hab : (graphF nA nbA).Adj a b) :
    (XS (hexInc (F := F)) j T.Fr T.φP T.φL (slotOf C pc fpt j K oV) (slotOf C pc fpt j K oU) (NSof K hubL)).Adj
      (iota C pc la lb j K hK kA aA lA a.val) (iota C pc la lb j K hK kA aA lA b.val) := by
  have hw : b.val ∈ nbA a.val := (adj_iff hLA).1 hab
  have h := hE a.val a.isLt b.val hw
  set u := a.val
  set w := b.val
  have md : ∀ x, x < K → x % K = x := fun x hx => Nat.mod_eq_of_lt hx
  simp only [auxE, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq, List.any_eq_true] at h
  rcases h with ((((((⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) |
      ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, t, ht, h5⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, t, ht, h5⟩) |
      ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, x, hx, h5⟩) | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, x, hx, h5⟩
  · -- line-side hub to its owner
    simp only [iota, h1, h2, if_true, if_neg (by decide : ¬ (2 = 0)), if_neg (by decide : ¬ (2 = 1))]
    refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl ?_⟩
    show Sum.inl (P_ C pc (aA w)) = Sum.inl (slotOf C pc fpt j K oV ⟨aA u % K, _⟩ (lA w : ZMod (2 * j + 1)))
    simp only [slotOf, md _ h3, zval h4, h5]
  · simp only [iota, h1, h2, if_true, if_neg (by decide : ¬ (2 = 0)), if_neg (by decide : ¬ (2 = 1))]
    refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr ?_⟩
    show Sum.inl (P_ C pc (aA u)) = Sum.inl (slotOf C pc fpt j K oV ⟨aA w % K, _⟩ (lA u : ZMod (2 * j + 1)))
    simp only [slotOf, md _ h3, zval h4, h5]
  · -- point-side hub to its owner's dual line
    simp only [iota, h1, h2, if_true, if_neg (by decide : ¬ (1 = 0)), if_neg (by decide : ¬ (3 = 0)),
      if_neg (by decide : ¬ (3 = 1)), if_neg (by decide : ¬ (3 = 2))]
    refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl ?_⟩
    show Sum.inr (L_ C la lb (aA w)) = Sum.inr (T.φP (slotOf C pc fpt j K oU ⟨aA u % K, _⟩ (lA w : ZMod (2 * j + 1))))
    simp only [slotOf, md _ h3, zval h4]
    rw [tφP T (hfpt _ (hoU _ h3 _ h4)), h5]
  · simp only [iota, h1, h2, if_true, if_neg (by decide : ¬ (1 = 0)), if_neg (by decide : ¬ (3 = 0)),
      if_neg (by decide : ¬ (3 = 1)), if_neg (by decide : ¬ (3 = 2))]
    refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr ?_⟩
    show Sum.inr (L_ C la lb (aA u)) = Sum.inr (T.φP (slotOf C pc fpt j K oU ⟨aA w % K, _⟩ (lA u : ZMod (2 * j + 1))))
    simp only [slotOf, md _ h3, zval h4]
    rw [tφP T (hfpt _ (hoU _ h3 _ h4)), h5]
  · -- a point on a line, same level
    simp only [iota, h1, h2, if_neg (by decide : ¬ (2 = 0)), if_neg (by decide : ¬ (2 = 1)), if_true,
      if_neg (by decide : ¬ (3 = 0)), if_neg (by decide : ¬ (3 = 1)), if_neg (by decide : ¬ (3 = 2))]
    rw [h3]
    have hi := tinc T h4 ht
    rw [h5] at hi
    exact (Typed.lvl _ _ _ _ _ _ _ _ _).map_rel (Hexagon.incGraph_adj_inl_inr.2 hi)
  · simp only [iota, h1, h2, if_neg (by decide : ¬ (2 = 0)), if_neg (by decide : ¬ (2 = 1)), if_true,
      if_neg (by decide : ¬ (3 = 0)), if_neg (by decide : ¬ (3 = 1)), if_neg (by decide : ¬ (3 = 2))]
    rw [h3]
    have hi := tinc T h4 ht
    rw [h5] at hi
    exact (Typed.lvl _ _ _ _ _ _ _ _ _).map_rel (Hexagon.incGraph_adj_inr_inl.2 hi)
  · -- the hub graph
    simp only [iota, h1, h2, if_true, if_neg (by decide : ¬ (1 = 0))]
    refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl ?_⟩
    show NSof K hubL ⟨aA u % K, _⟩ ⟨aA w % K, _⟩
    simp only [NSof, md _ h3, md _ h4, List.any_eq_true, Nat.beq_eq]
    exact ⟨x, hx, h5⟩
  · simp only [iota, h1, h2, if_true, if_neg (by decide : ¬ (1 = 0))]
    refine (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr ?_⟩
    show NSof K hubL ⟨aA w % K, _⟩ ⟨aA u % K, _⟩
    simp only [NSof, md _ h3, md _ h4, List.any_eq_true, Nat.beq_eq]
    exact ⟨x, hx, h5⟩

/-- The map of the auxiliary graph, as a graph homomorphism. -/
noncomputable def iotaHom {j K KF nA dA : ℕ} (hK : 0 < K) {fpt : ℕ → ℕ} (hfpt : ∀ f < KF, fpt f < N)
    {oV oU : ℕ → ℕ → ℕ} (hoV : ∀ v < K, ∀ i < 2 * j + 1, oV v i < KF) (hoU : ∀ v < K, ∀ i < 2 * j + 1, oU v i < KF)
    {hubL : ℕ → List ℕ} {kA aA lA : ℕ → ℕ} {nbA : ℕ → List ℕ}
    (hLA : LocalSpec dA nA nbA (auxC kA))
    (hE : ∀ u < nA, ∀ w ∈ nbA u, auxE N K (2 * j + 1) dP fpt ents oV oU hubL kA aA lA u w = true) :
    graphF nA nbA →g
      XS (hexInc (F := F)) j T.Fr T.φP T.φL (slotOf C pc fpt j K oV) (slotOf C pc fpt j K oU) (NSof K hubL) where
  toFun a := iota C pc la lb j K hK kA aA lA a.val
  map_rel' := fun {a b} h => auxHom T hK hfpt hoV hoU hLA hE a b h

/-- **Freed spread with a duality and cluster-assisted hubs, from tables.** -/
theorem main (j K KF : ℕ) (hK : 0 < K) (fpt : ℕ → ℕ) (hF : ∀ f < KF, gfOK N KF fpt fP f = true)
    (oV oU : ℕ → ℕ → ℕ) (invV invU : ℕ → List ℕ) (hOV : ∀ v < K, ownOK KF (2 * j + 1) oV invV v = true)
    (hOU : ∀ v < K, ownOK KF (2 * j + 1) oU invU v = true)
    (hInv : ∀ e < (2 * j + 1) * KF, invOK j invV invU e = true)
    (hubL hubR : ℕ → List ℕ) (hHub : ∀ v < K, hubOK K (q - j) hubL hubR v = true)
    (nA dA H m : ℕ) (nbA : ℕ → List ℕ) (kA aA lA : ℕ → ℕ) (hLA : LocalSpec dA nA nbA (auxC kA))
    (hE : ∀ u < nA, ∀ w ∈ nbA u, auxE N K (2 * j + 1) dP fpt ents oV oU hubL kA aA lA u w = true)
    (gens : List ((ℕ → ℕ) × (ℕ → ℕ))) (hP : ∀ g ∈ gens, PermSpec nA nbA g.1 g.2)
    (hH : ∀ g ∈ gens, ∀ v < H, g.1 v < H ∧ auxC kA (g.1 v) = auxC kA v)
    (hO : ∀ v, m ≤ v → v < H → ∃ g ∈ gens, g.1 v < v)
    (hB : ∀ s (hs : s < nA), s < m → ∀ w : Fin nA, w.val < H → auxC kA w.val = auxC kA s →
      (graphF nA nbA).edist w ⟨s, hs⟩ ≤ 6)
    (ixV ixU : ℕ → ℕ) (hIV : ∀ v < K, ixV v < H ∧ ixV v < nA ∧ kA (ixV v) = 0 ∧ aA (ixV v) = v)
    (hIU : ∀ v < K, ixU v < H ∧ ixU v < nA ∧ kA (ixU v) = 1 ∧ aA (ixU v) = v) (hjq : j ≤ q) :
    ∃ G : SimpleGraph (Fin ((2 * j + 1) * (N + N) + K + K)), IsBipartiteDegDiam G (q + 1 + j) 7 := by
  letI : Fintype (SPt F) := Fintype.ofFinite _
  letI : Fintype (HLine F) := Fintype.ofFinite _
  have hf1 : ∀ f < KF, fpt f < N ∧ fP (fpt f) = true := fun f hf => by
    have := hF f hf; simp only [gfOK, Bool.and_eq_true, Nat.blt_eq] at this; exact this.1
  have hinc : ∀ f, f + 1 < KF → fpt f < fpt (f + 1) := fun f hf => by
    have := hF f (by omega); simp only [gfOK, Bool.and_eq_true] at this; exact ltOfBlt (succ_of this.2 hf)
  have own : ∀ {o : ℕ → ℕ → ℕ} {inv : ℕ → List ℕ}, (∀ v < K, ownOK KF (2 * j + 1) o inv v = true) →
      ∀ v < K, ∀ i < 2 * j + 1, o v i < KF ∧ v ∈ inv (i * KF + o v i) := by
    intro o inv h v hv i hi
    have := allR_spec (h v hv) i (Nat.zero_le _) (by omega)
    simp only [Bool.and_eq_true, Nat.blt_eq, List.any_eq_true, Nat.beq_eq] at this
    obtain ⟨h1, x, hx, rfl⟩ := this
    exact ⟨h1, hx⟩
  have hoV : ∀ v < K, ∀ i < 2 * j + 1, oV v i < KF := fun v hv i hi => (own hOV v hv i hi).1
  have hoU : ∀ v < K, ∀ i < 2 * j + 1, oU v i < KF := fun v hv i hi => (own hOU v hv i hi).1
  have hzi : ∀ i : ZMod (2 * j + 1), i.val < 2 * j + 1 := fun i => ZMod.val_lt i
  have hFr : ∀ (o : ℕ → ℕ → ℕ), (∀ v < K, ∀ i < 2 * j + 1, o v i < KF) →
      ∀ v i, slotOf C pc fpt j K o v i ∈ T.Fr := by
    intro o ho v i
    have h := hf1 _ (ho v.val v.isLt i.val (hzi i))
    have : slotOf C pc fpt j K o v i = T.ptE ⟨fpt (o v.val i.val), h.1⟩ := rfl
    rw [this, T.mem_Fr]; exact h.2
  have hcount : ∀ {o : ℕ → ℕ → ℕ} {inv : ℕ → List ℕ}, (∀ v < K, ownOK KF (2 * j + 1) o inv v = true) →
      (∀ e < (2 * j + 1) * KF, (inv e).length ≤ j) →
      ∀ i (p : SPt F), (univ.filter (fun v => slotOf C pc fpt j K o v i = p)).card ≤ j := by
    intro o inv hO' hlen i p
    by_cases hne : (univ.filter (fun v => slotOf C pc fpt j K o v i = p)).Nonempty
    · obtain ⟨v0, hv0⟩ := hne
      have hv0' := (Finset.mem_filter.1 hv0).2
      set f0 := o v0.val i.val
      have hf0 := own hO' v0.val v0.isLt i.val (hzi i)
      have he : i.val * KF + f0 < (2 * j + 1) * KF := by
        have := hzi i
        calc i.val * KF + f0 < i.val * KF + KF := by omega
          _ = (i.val + 1) * KF := by ring
          _ ≤ (2 * j + 1) * KF := Nat.mul_le_mul_right _ this
      refine le_trans (Finset.card_le_card_of_injOn (fun v => v.val) (fun v hv => ?_)
        (fun v _ w _ h => Fin.ext h)) ((List.toFinset_card_le _).trans (hlen _ he))
      have hv' := (Finset.mem_filter.1 hv).2
      have hov := own hO' v.val v.isLt i.val (hzi i)
      have heq : P_ C pc (fpt (o v.val i.val)) = P_ C pc (fpt f0) := hv'.trans hv0'.symm
      have h1 := T.P_inj (hf1 _ hov.1).1 (hf1 _ hf0.1).1 heq
      have h2 : o v.val i.val = f0 := inj_of_succ hinc _ hov.1 _ hf0.1 h1
      simp only [Finset.mem_coe, List.mem_toFinset]
      rw [← h2]; exact hov.2
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  have hlV : ∀ e < (2 * j + 1) * KF, (invV e).length ≤ j := fun e he => by
    have := hInv e he; simp only [invOK, Bool.and_eq_true, Nat.ble_eq, lenP_eq] at this; exact this.1
  have hlU : ∀ e < (2 * j + 1) * KF, (invU e).length ≤ j := fun e he => by
    have := hInv e he; simp only [invOK, Bool.and_eq_true, Nat.ble_eq, lenP_eq] at this; exact this.2
  have hub1 : ∀ v < K, (hubL v).length ≤ q - j ∧ (hubR v).length ≤ q - j ∧ ∀ u ∈ hubL v, u < K ∧ v ∈ hubR u := by
    intro v hv
    have := hHub v hv
    simp only [hubOK, Bool.and_eq_true, Nat.ble_eq, lenP_eq, allP_eq, List.all_eq_true, Nat.blt_eq,
      List.any_eq_true, Nat.beq_eq] at this
    refine ⟨this.1.1, this.1.2, fun u hu => ?_⟩
    obtain ⟨h1, x, hx, rfl⟩ := this.2 u hu
    exact ⟨h1, hx⟩
  have hNV : ∀ v, (univ.filter (NSof K hubL v)).card ≤ q - j := by
    intro v
    refine le_trans (Finset.card_le_card_of_injOn (fun u => u.val) (fun u hu => ?_)
      (fun u _ w _ h => Fin.ext h)) ((List.toFinset_card_le _).trans (hub1 v.val v.isLt).1)
    have := (Finset.mem_filter.1 hu).2
    simp only [NSof, List.any_eq_true, Nat.beq_eq] at this
    obtain ⟨x, hx, hxe⟩ := this
    simp only [Finset.mem_coe, List.mem_toFinset]
    rw [hxe]; exact hx
  have hNU : ∀ u, (univ.filter (fun v => NSof K hubL v u)).card ≤ q - j := by
    intro u
    refine le_trans (Finset.card_le_card_of_injOn (fun v => v.val) (fun v hv => ?_)
      (fun v _ w _ h => Fin.ext h)) ((List.toFinset_card_le _).trans (hub1 u.val u.isLt).2.1)
    have := (Finset.mem_filter.1 hv).2
    simp only [NSof, List.any_eq_true, Nat.beq_eq] at this
    obtain ⟨x, hx, hxe⟩ := this
    simp only [Finset.mem_coe, List.mem_toFinset]
    have := ((hub1 v.val v.isLt).2.2 x hx).2
    rw [← hxe] at this
    exact this
  have hfpt : ∀ f < KF, fpt f < N := fun f hf => (hf1 f hf).1
  set ιg := iotaHom T hK hfpt hoV hoU hLA hE
  have hd := hub_edist hLA gens hP hH hO hB
  have hreach : ∀ a b : ℕ, a < nA → b < nA → a < H → b < H → auxC kA a = auxC kA b →
      Reach (XS (hexInc (F := F)) j T.Fr T.φP T.φL (slotOf C pc fpt j K oV) (slotOf C pc fpt j K oU) (NSof K hubL))
        (iota C pc la lb j K hK kA aA lA a) (iota C pc la lb j K hK kA aA lA b) 6 := by
    intro a b ha hb haH hbH hc
    have := reach_of_edist (hd ⟨a, ha⟩ ⟨b, hb⟩ haH hbH hc)
    exact this.map ιg
  have hubV : ∀ v v' : Fin K, Reach (XS (hexInc (F := F)) j T.Fr T.φP T.φL (slotOf C pc fpt j K oV)
      (slotOf C pc fpt j K oU) (NSof K hubL)) (.inr (.inl v)) (.inr (.inl v')) 6 := by
    intro v v'
    obtain ⟨a1, a2, a3, a4⟩ := hIV v.val v.isLt
    obtain ⟨b1, b2, b3, b4⟩ := hIV v'.val v'.isLt
    have := hreach _ _ a2 b2 a1 b1 (by simp [auxC, a3, b3])
    have e1 : iota C pc la lb j K hK kA aA lA (ixV v.val) = .inr (.inl v) := by
      simp only [iota, a3, if_true, a4, Nat.mod_eq_of_lt v.isLt]
    have e2 : iota C pc la lb j K hK kA aA lA (ixV v'.val) = .inr (.inl v') := by
      simp only [iota, b3, if_true, b4, Nat.mod_eq_of_lt v'.isLt]
    rwa [e1, e2] at this
  have hubU : ∀ u u' : Fin K, Reach (XS (hexInc (F := F)) j T.Fr T.φP T.φL (slotOf C pc fpt j K oV)
      (slotOf C pc fpt j K oU) (NSof K hubL)) (.inr (.inr u)) (.inr (.inr u')) 6 := by
    intro u u'
    obtain ⟨a1, a2, a3, a4⟩ := hIU u.val u.isLt
    obtain ⟨b1, b2, b3, b4⟩ := hIU u'.val u'.isLt
    have := hreach _ _ a2 b2 a1 b1 (by simp [auxC, a3, b3])
    have e1 : iota C pc la lb j K hK kA aA lA (ixU u.val) = .inr (.inr u) := by
      simp only [iota, a3, a4, Nat.mod_eq_of_lt u.isLt]; rfl
    have e2 : iota C pc la lb j K hK kA aA lA (ixU u'.val) = .inr (.inr u') := by
      simp only [iota, b3, b4, Nat.mod_eq_of_lt u'.isLt]; rfl
    rwa [e1, e2] at this
  have := exists_graph (q := q) (j := j) base_hexF T.spread_of T.dual_iff (fun x => deg_inc T.hq x)
    (slotOf C pc fpt j K oV) (slotOf C pc fpt j K oU) (NSof K hubL) (hFr oV hoV) (hFr oU hoU)
    (fun i x => by convert hcount hOV hlV i x) (fun i x => by convert hcount hOU hlU i x) hubV hubU hNV hNU hjq
  obtain ⟨G, hG⟩ := this
  have e : (2 * j + 1) * (Fintype.card (SPt F) + Fintype.card (HLine F)) + Fintype.card (Fin K) +
      Fintype.card (Fin K) = (2 * j + 1) * (N + N) + K + K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, T.hNP, T.hNL, Fintype.card_fin]
  exact ⟨_, BipartiteDD.isBipartiteDegDiam_comap (finCongr e) hG⟩

end Cell

end BipartiteDD.LeanAll.SpreadHub
