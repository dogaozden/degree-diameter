import Mathlib.Tactic.IntervalCases
import BipartiteDD.Haar.R225792.TabDefs
import BipartiteDD.Haar.R225792.TabP0
import BipartiteDD.Haar.R225792.TabP1
import BipartiteDD.Haar.R225792.TabP2
import BipartiteDD.Haar.R225792.TabP3
import BipartiteDD.Haar.R225792.TabQ00
import BipartiteDD.Haar.R225792.TabQ01
import BipartiteDD.Haar.R225792.TabQ02
import BipartiteDD.Haar.R225792.TabQ03
import BipartiteDD.Haar.R225792.TabQ04
import BipartiteDD.Haar.R225792.TabQ05
import BipartiteDD.Haar.R225792.TabQ06
import BipartiteDD.Haar.R225792.TabQ07
import BipartiteDD.Haar.R225792.TabQ08
import BipartiteDD.Haar.R225792.TabQ09
import BipartiteDD.Haar.R225792.TabQ10
import BipartiteDD.Haar.R225792.TabQ11
import BipartiteDD.Haar.R225792.TabQ12
import BipartiteDD.Haar.R225792.TabQ13
import BipartiteDD.Haar.R225792.TabQ14
import BipartiteDD.Haar.R225792.TabQ15
import BipartiteDD.Haar.R225792.TabInv

/-! The multiplication and inverse tables are checked against the group operations, chunk by chunk (one
module per chunk, to keep each kernel check small). The chunks are assembled into the statements
`mP_ok`, `mQ_ok`, `iP_ok`, `iQ_ok` over all indices. -/

namespace BipartiteDD.Haar.R225792

open M2

theorem mP_ok : ∀ i < 168, mPcheck i = true := by
  have h : ∀ c < 4, ∀ r < 42, mPcheck (42 * c + r) = true := by
    intro c hc r hr
    interval_cases c
    · exact chunkP0 r hr
    · exact chunkP1 r hr
    · exact chunkP2 r hr
    · exact chunkP3 r hr
  intro i hi
  have := h (i / 42) (by omega) (i % 42) (by omega)
  rwa [show 42 * (i / 42) + i % 42 = i by omega] at this

theorem mQ_ok : ∀ i < 336, mQcheck i = true := by
  have h : ∀ c < 16, ∀ r < 21, mQcheck (21 * c + r) = true := by
    intro c hc r hr
    interval_cases c
    · exact chunkQ00 r hr
    · exact chunkQ01 r hr
    · exact chunkQ02 r hr
    · exact chunkQ03 r hr
    · exact chunkQ04 r hr
    · exact chunkQ05 r hr
    · exact chunkQ06 r hr
    · exact chunkQ07 r hr
    · exact chunkQ08 r hr
    · exact chunkQ09 r hr
    · exact chunkQ10 r hr
    · exact chunkQ11 r hr
    · exact chunkQ12 r hr
    · exact chunkQ13 r hr
    · exact chunkQ14 r hr
    · exact chunkQ15 r hr
  intro i hi
  have := h (i / 21) (by omega) (i % 21) (by omega)
  rwa [show 21 * (i / 21) + i % 21 = i by omega] at this

end BipartiteDD.Haar.R225792
