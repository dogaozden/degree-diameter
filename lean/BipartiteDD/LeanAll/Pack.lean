import BipartiteDD.LeanAll.HexLocal

/-! # Packed data

A tree leaf costs about 1.3 kB of olean whatever it holds, so the data files of the large cells store many
fixed-width fields per leaf: `lookP T D L w i` is field `i` (`w` bits) of a tree of depth `D` whose leaves hold
`2 ^ L` fields each, low field first. Lists of a fixed length are packed into one field (`unpackL`, `unpack3`), and
so are the certificates of `HexLocal` (`decCert`). The checks are unchanged: they take functions, and these are
functions. -/

namespace BipartiteDD.LeanAll.Pack

open BipartiteDD.Fast BipartiteDD.LeanAll.Orbit2

/-- `2 ^ w - 1`. -/
def maskW (w : ℕ) : ℕ := Nat.sub (Nat.pow 2 w) 1

/-- Field `i` of `w` bits. -/
noncomputable def lookP (T : BipartiteDD.Fast.Tree ℕ) (D L w i : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight (look T D (Nat.shiftRight i L)) (Nat.mul w (Nat.land i (maskW L)))) (maskW w)

/-- `n` fields of `w` bits, low first. -/
def unpackL (w : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => Nat.land x (maskW w) :: unpackL w n (Nat.shiftRight x w)

/-- `n` triples of `a`, `b`, `c` bits, low first. -/
def unpack3 (a b c : ℕ) : ℕ → ℕ → List (ℕ × ℕ × ℕ)
  | 0, _ => []
  | n + 1, x => (Nat.land x (maskW a), Nat.land (Nat.shiftRight x a) (maskW b),
      Nat.land (Nat.shiftRight x (a + b)) (maskW c)) :: unpack3 a b c n (Nat.shiftRight x (a + b + c))

/-- `n` quadruples of `a`, `b`, `c`, `d` bits, low first. -/
def unpack4 (a b c d : ℕ) : ℕ → ℕ → List (ℕ × ℕ × ℕ × ℕ)
  | 0, _ => []
  | n + 1, x => (Nat.land x (maskW a), Nat.land (Nat.shiftRight x a) (maskW b),
      Nat.land (Nat.shiftRight x (a + b)) (maskW c), Nat.land (Nat.shiftRight x (a + b + c)) (maskW d)) ::
      unpack4 a b c d n (Nat.shiftRight x (a + b + c + d))

/-- The `e`-part of a certificate: `n` entries, each a code (`wx` bits) and `p` triples (`we`, `wc`, `wc`). -/
def decE (p wx we wc : ℕ) : ℕ → ℕ → List (ℕ × List (ℕ × ℕ × ℕ))
  | 0, _ => []
  | n + 1, x => (Nat.land x (maskW wx), unpack3 we wc wc p (Nat.shiftRight x wx)) ::
      decE p wx we wc n (Nat.shiftRight x (wx + p * (we + 2 * wc)))

/-- The `f`-part: `n` entries, each a triple (`wx`, `wc`, `wc`) and `p` quadruples (`we`, `wc`, `wc`, `wp`). -/
def decF (p wx we wc wp : ℕ) : ℕ → ℕ → List ((ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ))
  | 0, _ => []
  | n + 1, x => ((Nat.land x (maskW wx), Nat.land (Nat.shiftRight x wx) (maskW wc),
      Nat.land (Nat.shiftRight x (wx + wc)) (maskW wc)), unpack4 we wc wc wp p (Nat.shiftRight x (wx + 2 * wc))) ::
      decF p wx we wc wp n (Nat.shiftRight x (wx + 2 * wc + p * (we + 2 * wc + wp)))

/-- A `HexLocal` certificate from one number. -/
def decCert (p wx we wc wp x : ℕ) : HexLocal.Cert :=
  (decE p wx we wc (p + 1) x, decF p wx we wc wp (p + 1) (Nat.shiftRight x ((p + 1) * (wx + p * (we + 2 * wc)))))

end BipartiteDD.LeanAll.Pack
