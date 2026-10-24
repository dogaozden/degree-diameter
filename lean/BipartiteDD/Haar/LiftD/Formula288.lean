import BipartiteDD.Basic
import BipartiteDD.Fast

/-! The voltage lift of a 4-vertex cubic base graph over `G = Z3^2 x|_M Z8`, `M = [[0,2],[1,0]]`, with the voltages of
`research/lifts/sols/c1r_d3D8_n288_b2_3_0_aff302108_s1.txt`.

Vertices are `(u, g)` with `u < 4` and `g = (x, y, j)` coded as `x + 3 y + 9 j`, numbered `72 u + code g`.
The product is `(v, j) (w, l) = (v + M^j w, j + l)`. A base edge `u – w` with voltage `α` gives the lift edges
`(u, g) ~ (w, g α)` for all `g`. The neighbour lists below are read off from that rule: forward edges use `α`,
backward edges use the inverse `α⁻¹` (both listed in `baseEdges`). -/

namespace BipartiteDD.LiftD

/-- `M^j p` for `M = [[0,2],[1,0]]` over `Z3`, where `M (x, y) = (2 y, x)`. -/
def mpow : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | j + 1, p => mpow j (2 * p.2 % 3, p.1)

/-- The group law on `(x, y, j)`: `(v, j) (w, l) = (v + M^j w, j + l)`. -/
def gmul (g h : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  let w := mpow g.2.2 (h.1, h.2.1)
  ((g.1 + w.1) % 3, (g.2.1 + w.2) % 3, (g.2.2 + h.2.2) % 8)

/-- Decode a code `x + 3 y + 9 j` to `(x, y, j)`. -/
def gdec (k : ℕ) : ℕ × ℕ × ℕ := (k % 3, k / 3 % 3, k / 9)

/-- Encode `(x, y, j)` as `x + 3 y + 9 j`. -/
def genc (g : ℕ × ℕ × ℕ) : ℕ := g.1 + 3 * g.2.1 + 9 * g.2.2

/-- Base edges `(u, w, α, α⁻¹)`: the lift has `(u, g) ~ (w, g α)` for every `g`. -/
def baseEdges : List (ℕ × ℕ × (ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ)) := [
  (0, 2, (0, 0, 0), (0, 0, 0)),
  (0, 2, (2, 0, 3), (0, 1, 5)),
  (0, 3, (0, 0, 0), (0, 0, 0)),
  (1, 2, (0, 0, 0), (0, 0, 0)),
  (1, 3, (1, 1, 3), (1, 2, 5)),
  (1, 3, (1, 1, 2), (1, 1, 6))]

/-- Neighbours of vertex `v`, as numbers: forward edges `(w, g α)` and backward edges `(a, g α⁻¹)`. -/
def nbrNat (v : ℕ) : List ℕ :=
  let u := v / 72
  let g := gdec (v % 72)
  (baseEdges.filterMap fun e => if e.1 = u then some (e.2.1 * 72 + genc (gmul g e.2.2.1)) else none) ++
  (baseEdges.filterMap fun e => if e.2.1 = u then some (e.1 * 72 + genc (gmul g e.2.2.2)) else none)

/-- The neighbour lists of the lift, indexed by vertex number. -/
def adjL : List (List (Fin 288)) :=
  (List.range 288).map fun v => (nbrNat v).map fun w => ⟨w % 288, Nat.mod_lt _ (by decide)⟩

/-- The 2-colouring: the base vertices `2, 3` form one side, `0, 1` the other. -/
def colL : List Bool := (List.range 288).map fun v => decide (2 ≤ v / 72)

end BipartiteDD.LiftD
