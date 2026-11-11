# VERIFY: lean-d7family (Corollary 9.1 of D7_HEXAGON.md)

Verifier session (Sonnet), independent of the worker's logs. Result: **the claim holds as stated. No weakening found.**

## What was checked

Worker branch `claude/d7-family-diameter-formalize-sqtpmv` @ `9d96789`. Note `claude/d7-hexagon-theorems-4w1prt`.
Lean 4.34.1 + Mathlib v4.34.1 (cache downloaded with `lake exe cache get`; Lean itself installed from the release tarball).

1. **Merge.** `origin/master` is an ancestor of the worker branch, so the merge was a fast-forward. No conflicts.
2. **Builds** (foreground, one at a time, `lake build BipartiteDD.LeanMaxx.D7Family.<M>`): Hub, Assembly, Odd, Even, Main, Axioms.
   All exit 0, no `error`, no `sorry` warning. (Only unused-section-variable linter warnings in the old lean-all files.)
3. **Axioms.** `lake env lean BipartiteDD/LeanMaxx/D7Family/Axioms.lean` regenerated; `diff` against the committed
   `Axioms.out.txt` is empty. All six theorems (`d7_of_sets`, `d7_odd`, `d7_family_odd`, `d7_even`, `d7_family_even`,
   `d7_family`) depend on exactly `[propext, Classical.choice, Quot.sound]`.
   I also added a scratch file with my own restatement (below); its `#print axioms` gives the same three.
   `lake env leanchecker BipartiteDD.LeanMaxx.D7Family.Main` exits 0 with no output. See the last section: the `--fresh` full replay did not finish.
4. **Grep** (`sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|ofReduceBool|opaque|instance|set_option|macro|elab|notation|attribute|@[`) over the six files:
   - `set_option linter.unusedSectionVars false` (Assembly.lean:21, Hub.lean:119): linter switch, harmless.
   - `noncomputable instance : Fintype (Node d m)` (Hub.lean:47), built with `Fintype.ofEquiv`: a data instance, harmless (Fintype is a subsingleton).
   - `#print axioms` lines in Axioms.lean; the word "local" in a docstring.
   - Nothing else. The same grep over all 47 transitive `BipartiteDD.*` imports (the lean-all modules) finds nothing.
5. **Statement fidelity.**
   `d7_family (q : ℕ) (hq : IsPrimePow q) (h5 : 5 ≤ q) : ∃ G : SimpleGraph (Fin (6 * ((q^6 - 1)/(q - 1)) + 2 * (q^2 + 1))), IsBipartiteDegDiam G (q + 2) 7`.
   - `IsPrimePow` is Mathlib's, so odd and even q are both covered (`d7_family` splits on `Nat.even_or_odd`).
   - `N(q) = (q^6-1)/(q-1)` is natural-number division; it is exact, and `Nq_eq` proves it equals `(q+1)(1+q^2+q^4)`.
     q = 5 gives 6·3906 + 52 = 23488, the value in the note's text.
   - `IsBipartiteDegDiam G d D := G.Colorable 2 ∧ (∀ v, (G.neighborSet v).ncard ≤ d) ∧ G.ediam ≤ D` (BipartiteDD/Basic.lean:10).
     `ediam ≤ 7` forces connectivity, so this is the real property: bipartite, max degree ≤ q+2, diameter ≤ 7.
   - I restated it with the definition unfolded into Mathlib terms (`G.Colorable 2 ∧ (∀ v, (G.neighborSet v).ncard ≤ q+2) ∧ G.ediam ≤ 7`)
     in a scratch file and closed it with `d7_family`; it typechecks. Instances q = 5 and q = 8 also typecheck.
     Cor. 9.1 in the note reads `n_b(q+2,7) ≥ 6N(q) + 2 min(q²+1, κ(q−1))`, "which is 6N(q)+2(q²+1) for every q ≥ 5"; the Lean statement is that value.
   - The statement does not mention the hexagon, so the correctness of the intermediate definitions cannot make it false;
     only the kernel check matters, and that passes.
6. **lean-all dependencies unchanged.** `git diff origin/claude/lean-all-jvj7b0 HEAD -- lean` touches only the six new
   `LeanMaxx/D7Family/*.lean` files plus `Axioms.out.txt`; no existing Lean file is modified. (The only other differences
   against lean-all are README.md, `papers/*.pdf` and `research/lean-maxx/STATUS-d7family.md`, which come from master or are the worker's status file.)
   The 47 transitive imports are Basic, Doubling.*, GQ4.*, Hexagon.*, HexagonD.{Pi,PiCount,Polygon,Spread}, HexagonD7.*, HexagonEven.* (list: `git`-reproducible by following `import` lines from `D7Family/Main.lean`).
7. **Hypotheses of `d7_of_sets` are discharged, not assumed**, for every q:
   - `5 ≤ card F`: from `5 ≤ q` and `card K = p^k` (`GaloisField.card`).
   - Odd: `NeZero (2:K)` is derived from `p ≠ 2`, which is derived from `Odd q`. `a` non-square comes from `FiniteField.exists_nonsquare`.
     R = image of `qpt a` over `Option (F × F)`; `card = q²+1` by `qpt_injective` and `Fintype.card_option/prod`; pairwise `Bf ≠ 0` is `bf_qpt_ne`
     (proved: `Bf = (y−y')² − a(x−x')²` is nonzero because a is a non-square; `Bf(vq, vinf) = 1`).
     S = a `q²+1`-subset of the `q³+1` lines of `SLine (-a)` (`card_sline`); pairwise `Opp` from `sline_opp`.
   - Even: `(2:K)=0` from `CharP`; β with `t²+t+β² ≠ 0` for all t is proved (`exists_beta`: `t ↦ t²+t` is not injective hence not surjective on a finite field;
     every element is a square in char 2). R = image of `qptE β`; `Bf = (Δx+βΔy)² − ΔxΔy ≠ 0` proved in `Bf_vqE_ne`; S from `SLineE (β²)` with `card_slineE`, `sline_oppE`.
   - `hRc`, `hSc` (both `q²+1`), `hR`, `hS` are all proofs inside `d7_odd`/`d7_even`, none is a hypothesis of `d7_family`.
   - `d7_of_sets` itself uses `genPolygonGraph_hexagon_even` (the hexagon axioms for H(q)), `exists_local_duality` and `exists_graph` from lean-all, unchanged, covered by the axiom check.

## Weakenings

None found. Differences in form only: the theorem is an existence statement for the graph on exactly `6N(q)+2(q²+1)` vertices (the lower bound `n_b ≥ …` follows by the usual padding/monotonicity, which the note's `n_b` convention supplies; the Lean statement is the construction itself).
The case q = 4 (where the note says κ(3)=7 < 17) is correctly excluded by `5 ≤ q`.

## Environment notes

- The cloud image has no Lean. I unpacked the `lean-4.34.1-linux.tar.zst` release into `~/.elan/toolchains/leanprover--lean4---v4.34.1` (via Python `zstandard`, no `zstd` binary), then `lake exe cache get` (about 2.5 min), then the builds above (Hub 46 s incl. the old lean-all chain, Assembly 2 min, Odd 45 s, Even 52 s, Main 16 s).
- Scratch restatement file: `scratchpad/v/Fid.lean` (not committed; contents quoted in item 5).

## leanchecker --fresh

Not completed. `leanchecker --fresh` (replays all of Mathlib plus the lean-all modules through the kernel, one thread) ran for 30 minutes
(7 GB RSS) and was stopped by the 30-minute background limit; I did not restart it. So the evidence for the kernel check is: the
normal `lake build` of every module (Lean elaborator plus kernel), the regenerated `#print axioms` output, and the plain
`leanchecker ... D7Family.Main` run (exit 0). The fresh full replay is an optional extra that someone with a longer budget can run:
`cd lean && lake env leanchecker --fresh BipartiteDD.LeanMaxx.D7Family.Main`.
