# Job "lemma": Haar diameter lemma for every diameter

Status: **done** for the statements below, with the caveats listed at the end. Branch: `claude/lean-haard-lemma-c4hhmf`
(the session's designated branch; the brief's `lean-haarD-lemma` name was not used).

## What is proved (`lean/BipartiteDD/Haar/GraphD.lean`)

Definitions. For `S : Finset G` in a group `G`:

- `IsLeftWord S n x`: `x` is a product of at most `n` factors `s⁻¹ * t`, `s, t ∈ S`
  (a list of pairs `(s, t)` of length ≤ `n`).
- `IsRightWord S n x`: the same with factors `s * t⁻¹`.

Theorems (on `haarGraph S`, the graph of `Graph.lean`, vertices `G ⊕ G`):

| Theorem | Hypotheses | Conclusion |
|---|---|---|
| `haar_ediam_le_odd` | `S.Nonempty`, `∀ x, IsLeftWord S n x`, `∀ x, IsRightWord S n x` | `ediam ≤ 2n+1` |
| `haar_ediam_le_even` | `∀ x, ∃ s ∈ S, IsLeftWord S n (s⁻¹ * x)` | `ediam ≤ 2n+2` |

`n` is arbitrary in ℕ; the brief's `n ≥ 1` is not needed (for `n = 0` the odd statement still holds, because of `S.Nonempty`).
`G` is any group, not only a finite one.

Matching statements with the degree bound, in `Main.lean`:
`haar_isBipartiteDegDiam_odd` and `haar_isBipartiteDegDiam_even` give `IsBipartiteDegDiam (haarGraph S) S.card (2n+1)` and
`(2n+2)`.

**The even statement.** For `D = 2n+2` the covering is `G = S · (S⁻¹S)^n`, i.e. every element is a word of `2n+1`
letters `s, s⁻¹, …, s` (`D − 1` letters). This is the criterion in `research/frontier/PLAN.md`, "Diameter criterion
at even D": a walk from `(e,A)` to `(x,B)` of odd length `≤ D − 1` exists iff `x` is such a word, and right
multiplication is transitive on each side. The brief pointed at `HAAR_GEN_NOTES.md §covering`, but that file has no
such section; the criterion lives in `PLAN.md`. The even cost in `haar_gen3.c` (`#B not within D−1 of (e,A)`) is the
same condition. The odd cost (`#A within D−1 of (e,A)` and `#B within D−1 of (e,B)`) is the pair of hypotheses above.

**The n = 2 check.** `haar_ediam_le_five` in `Main.lean` is now the corollary `haar_ediam_le_odd hS 2` with the
four-product hypotheses turned into `IsLeftWord S 2`, `IsRightWord S 2` (`isLeftWord_two_of_four`,
`isRightWord_two_of_four`). Same statement as before, so the record files are unaffected. `Main` also keeps the
transported (`W`-level) version `ediam_le_five_of`, unchanged; that proof duplicates the new one and could be
removed later.

## Certificate form (decidable, no enumeration of words)

- `wordOK sL n w`: index word `w` (pairs of indices into a list `sL` of elements of `S`) has length ≤ `n`, all indices in range.
- `leftCertOK sL tgt n cert`, `rightCertOK …`: for each `i < tgt.length`, entry `cert[i]` is a word whose product is
  `tgt[i]`. `evenCertOK …`: entry `j` is `(i, w)` with `sL[i] * product(w) = tgt[j]`.
- Each is a `Bool` function. `decide +kernel` evaluates it; no word is enumerated by Lean.
- `isLeftWord_of_cert`, `isRightWord_of_cert`, `isEven_of_cert` turn a successful check, a numbering
  `idx : G → ℕ` with `tgt.getD (idx x) 1 = x`, and `∀ s ∈ sL, s ∈ S` into the covering hypotheses above.

A record proof would: generate `cert` by a script (as `research/d5/make_haar_cert_2640.py` does for the current records),
state `tgt` as the list of elements in the numbering of the group, run `decide +kernel` on the check, and apply the lemma.

**Test.** `namespace BipartiteDD.Haar.Cycle10` (end of `GraphD.lean`): the Haar graph of `ℤ/5` with `S = {0, 1}`
(the 10-cycle) is checked by all three certificates. `ediam_le_five` (odd, `n = 2`) and `ediam_le_six` (even, `n = 2`)
are proved end to end from `decide +kernel` checks. The 10-cycle has diameter 5, so `≤ 5` is sharp there.

## Axioms

`#print axioms` for every new theorem gives `[propext, Classical.choice, Quot.sound]` only (see
`lean/Axioms.out.txt`, last 11 lines, and the new `#print` lines at the end of `lean/Axioms.lean`). No `sorry`,
`admit`, `native_decide`, or new `axiom`.

## Build

- Toolchain `leanprover/lean4:v4.34.1`, Mathlib from `lake exe cache get` (ok, 8908 files).
- `lake build BipartiteDD.Haar.GraphD`: ok, no warnings.
- `lake build BipartiteDD.Haar.Main`: ok, no warnings.
- `lake build BipartiteDD.Haar.Record1152`: see the note at the end (run for regression).

## Not done / caveats

1. **Converse of the even criterion** (`diam ≤ 2n+2 ⇒ covering`) is not proved; only the direction needed for records.
   The converse is a short argument (the PLAN.md remark) and would be the next lemma if wanted.
2. **`Axioms.out.txt` was not fully regenerated.** `lean/Axioms.lean` imports the whole library closure (about 9,000
   modules per `CHECK.txt`, with OOM history). I checked the new theorems with a small file importing `Haar.Main`
   (`lake env lean`), and appended those printed lines to `Axioms.out.txt`. The `#print axioms` output of a theorem
   depends only on its own dependency closure, so these lines match what the full run prints for them.
3. **Records not migrated.** The `Record*.lean` / `Cert*.lean` files still use the four-product covers. They still
   build against the changed `Main` (see the build note below). Migrating them to the certificate form is a separate job.
4. **Duplicate `W`-level proof** in `Main.lean` (`ediam_le_five_of`) left in place.
5. Code comments cite `research/frontier/PLAN.md` for the even criterion; the brief's `HAAR_GEN_NOTES.md §covering` does not exist.

## Commits

Work is on `claude/lean-haard-lemma-c4hhmf`: `d3f62ff` (GraphD), then the Main/Axioms/STATUS changes.
