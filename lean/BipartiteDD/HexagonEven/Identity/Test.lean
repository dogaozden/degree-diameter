import BipartiteDD.HexagonEven.Pi

namespace BipartiteDD.HexagonEven.IdTest

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

def JA (d α β : F) (x : V7 F) : F := (d + 1) * x 0 + d * α * x 2 + d ^ 2 * x 4 + (α + d * β) * x 5
def JB (d α β : F) (x : V7 F) : F := β * x 0 + x 1 + α * β * x 2 + (α + d * β) * x 4 + β ^ 2 * x 5 + x 6
def JC (x : V7 F) : F := x 2 + x 5
def JD (d α β : F) (x : V7 F) : F := x 0 + (α + β) * x 2 + d * x 4 + β * x 5
def JF (d : F) (x : V7 F) : F := d * x 2
def JG (d α β : F) (x : V7 F) : F := (α + β) * x 0 + d * x 1 + α ^ 2 * x 2 + d * α * x 4 + α * β * x 5

def JE (d α β : F) (x : V7 F) : V7 F :=
  ![JA d α β x, JB d α β x, JC x, JA d α β x + d * JD d α β x + α * JC x + β * JF d x,
    JD d α β x, JF d x, JG d α β x]

theorem test_a (d α β : F) (x : V7 F) (hx : x 0 + x 3 + d * x 4 + α * x 2 + β * x 5 = 0)
    (h2 : (2 : F) = 0) :
    JE d α β (JE d α β x) = JE d α β x + d • x := by
  have e3 : x 3 = x 0 + d * x 4 + α * x 2 + β * x 5 := by
    linear_combination hx - (x 0 + d * x 4 + α * x 2 + β * x 5) * h2
  funext i
  fin_cases i
  · simp [JE, JA, JB, JC, JD, JF, JG, e3]
    done
  all_goals sorry

end BipartiteDD.HexagonEven.IdTest
