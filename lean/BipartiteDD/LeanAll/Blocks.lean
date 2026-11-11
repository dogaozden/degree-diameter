import BipartiteDD.LeanAll.Swar

/-! # Packed ramps by blocks

For a batch of `p n` slots the constants `RD = pkF w (fun j => j / n) (p n)` and `RZ = pkF w (fun j => j % n) (p n)`
are numbers of `40 p n` bits. Checking such a literal against `pkF` in the kernel costs memory quadratic in `p n`;
here they are written as sums of `p` blocks of `n` fields (`blk`), equal to the `pkF` forms by `ramp_div`,
`ramp_mod` and `ramp_neg` (proved once, no evaluation). -/

namespace BipartiteDD.LeanAll.Swar

/-- `Σ_{d < p} 2 ^ (w n d) * g d`. -/
def blk (w n : ℕ) (g : ℕ → ℕ) (p : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun d acc => acc + 2 ^ (w * n * d) * g d) p

theorem pkF_append (w : ℕ) (f : ℕ → ℕ) (a : ℕ) :
    ∀ b, pkF w f (a + b) = pkF w f a + 2 ^ (w * a) * pkF w (fun j => f (a + j)) b := by
  intro b
  induction b with
  | zero => simp [pkF]
  | succ b ih =>
    rw [← Nat.add_assoc, pkF_succ, ih, pkF_succ, show w * (a + b) = w * a + w * b by ring, pow_add]
    ring

theorem pkF_blocks (w n : ℕ) (f : ℕ → ℕ) :
    ∀ p, pkF w f (p * n) = blk w n (fun d => pkF w (fun z => f (d * n + z)) n) p := by
  intro p
  induction p with
  | zero => simp [pkF, blk]
  | succ p ih =>
    rw [Nat.succ_mul, pkF_append, ih]
    show _ = blk w n _ p + 2 ^ (w * n * p) * _
    rw [show w * (p * n) = w * n * p by ring]

theorem blk_congr {w n p : ℕ} {g h : ℕ → ℕ} (e : ∀ d, g d = h d) : blk w n g p = blk w n h p := by
  rw [show g = h from funext e]

theorem ramp_div (w n p : ℕ) (hn : 0 < n) :
    pkF w (fun j => j / n) (p * n) = blk w n (fun d => d * pkF w (fun _ => 1) n) p := by
  rw [pkF_blocks]
  apply blk_congr
  intro d
  rw [← pkF_const]
  apply pkF_congr
  intro z hz
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hz, Nat.zero_add]

theorem ramp_mod (w n p : ℕ) :
    pkF w (fun j => j % n) (p * n) = blk w n (fun _ => pkF w (fun z => z) n) p := by
  rw [pkF_blocks]
  apply blk_congr
  intro d
  apply pkF_congr
  intro z hz
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]

theorem ramp_neg (w n p q : ℕ) (hn : 0 < n) :
    pkF w (fun j => (q - j / n) % q) (p * n) = blk w n (fun d => (q - d) % q * pkF w (fun _ => 1) n) p := by
  rw [pkF_blocks]
  apply blk_congr
  intro d
  rw [← pkF_const]
  apply pkF_congr
  intro z hz
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hz, Nat.zero_add]

end BipartiteDD.LeanAll.Swar
