import BipartiteDD.LeanAll.Core.HaarCore
import BipartiteDD.LeanAll.Blocks

/-! # The core constants as `Swar` terms

`Core.blk` and `Core.onesC` are elaborated without Mathlib, so their powers use core's `Pow ℕ ℕ` instance; these
lemmas restate them with the `Swar` forms (proved with the arguments symbolic, so nothing is evaluated). -/

namespace BipartiteDD.LeanAll.Core

open BipartiteDD.LeanAll.Swar

theorem blk_eq (w n : ℕ) (g : ℕ → ℕ) (p : ℕ) : Core.blk w n g p = Swar.blk w n g p := rfl

theorem onesC_eq (w N : ℕ) (hw : 1 ≤ w) : onesC w N = pkF w (fun _ => 1) N := by
  rw [pkF_one_eq w N hw]
  rfl

end BipartiteDD.LeanAll.Core
