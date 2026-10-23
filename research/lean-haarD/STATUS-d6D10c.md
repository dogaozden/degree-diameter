# STATUS d6D10c: Δ6·D10 506,160 in Lean

**Done.** `nb_6_10_haar` builds, and `D6D10/Axioms.out.txt` reads
`'nb_6_10_haar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `native_decide`, `axiom`, and no `maxHeartbeats` raised anywhere (the record module builds at the
default 200000 heartbeats, in about 2 s once the 45 stage modules are built).

Branch: `claude/lean-haar-d6d10c-v26k8m`, started from `claude/lean-haar-d6d10-pz982l` and rebased onto `origin/master`
(e3b9561). The earlier status note `STATUS-d6D10.md` (blocked at `isDefEq`) is superseded by this one.

## The obstacle and the fix

`haar_isBipartiteDegDiam10_of_equiv SS equiv506160 cover` timed out at the `cover` argument. Diagnosis, from isolated
test files (not committed):

- The lemma's hypothesis writes `*` and `⁻¹` through the `[Group G]` instance (`MulOneClass.toMul (…Group.toDivInvMonoid inst)`).
  The `cover` statement wrote them through the direct instances of `PGL37Z5.Grp = PGL37.Grp × Multiplicative (ZMod 5)`
  (`Prod.instMul`, `PGL37.instMul`, …). The two terms are defeq but not syntactically equal.
- Comparing the two is cheap when the statement has no binders (a nine-letter product of variables converts in about
  1 s). Under the `∃ x₁ ∈ S, …` binders it blows up: even with `S` and `hc` as variables and no `SS` at all, the lemma
  application times out at 200000 heartbeats. Marking `SS` irreducible does not help (the blow-up is not in `SS`).
  Adding `Mul`/`Inv` instances derived from the group structure does not help either.
- The lemma application is cheap when the hypothesis has the **lemma's own** instance path. So the covering condition is
  now a definition: `def CoverHyp {G} [Group G] (S : Finset G) : Prop := ∀ g, ∃ x₁ ∈ S, …, g = x₁ * (x₂⁻¹ * …)`
  (`Words.lean`). `cover : CoverHyp SS` is proved by unfolding it, and `Record506160.lean` passes `cover` directly.
  Checked: `haar_isBipartiteDegDiam10_of_equiv SS expEquiv hc` with `hc : CoverHyp SS` elaborates in seconds.
- The word `wordG c` is now `wordOf (sel (dig c 0)) … (sel (dig c 8))`, where `wordOf` is the nine-letter product written
  once for any `[Group G]`. Its unfolding then matches `CoverHyp`'s body term for term, so the last step of `cover` is a
  delta step. (With the old right-nested product written inline, that last step timed out at 200000 heartbeats.)
- The brief's suggested fix was tried first: `have hc : <exact type> := cover` is accepted, but passing `hc` to the
  lemma still times out, because the mismatch is between the two instance paths, not between the names. The `CoverHyp`
  form avoids it; no `irreducible` marks were needed (`SS` made irreducible still timed out).

## Modules

All in `lean/BipartiteDD/Haar/` (new files under `D6D10/` or the existing record path; no master file duplicated):

| Module | Content |
|---|---|
| `D6D10/Stage00…Stage44` | 45 certificate stages, each checked by `decide +kernel` (built one at a time; parallel builds were OOM-killed, exit 137) |
| `D6D10/Cover.lean` | `exC`: every index has a code, from the stages (built) |
| `D6D10/Words.lean` | `sel`, `SS`, `wordOf`, `wordG`, `wordG_eq`, `CoverHyp`, `cover : CoverHyp SS` (rebuilt: the fix) |
| `Record506160.lean` | `nb_6_10_haar` (builds; no `set_option`) |
| `D6D10/Axioms.lean`, `D6D10/Axioms.out.txt` | the axioms check (three standard axioms only) |

The stage, cover and check modules are unchanged from the earlier branch. `Diam10.lean`, `PGL37*.lean` and `Check.lean`
are unchanged.

## Build notes for the next job

- Toolchain: elan with `leanprover/lean4:v4.34.1`; `lake exe cache get` takes about 2.5 min.
- `lake build` of the whole stage set in parallel ran out of memory (exit 137). Building `Stage00 … Stage44` one by one
  took about a minute per stage on this machine; `Cover`, `Words`, `Record506160` then took seconds each.
- `lake build` has no `-j` flag in this toolchain; use a serial loop over the stage modules when memory is tight.

## Deviations from the brief

- The fix is a definition (`CoverHyp`, `wordOf`) rather than the irreducible marks and the copied D7D9 cover pattern.
  The D7D9 pattern (`cover1 cover2`) worked because the SL(2,31) product is a plain structure; the PGL(2,37) product is
  defined through normal forms, and its expansion is what made the term-by-term comparison expensive.
- The record is still not imported by `BipartiteDD.lean`, as before.
