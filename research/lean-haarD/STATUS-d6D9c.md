# STATUS d6D9c: Δ6·D9 127,296 in Lean

**Done.** `nb_6_9_127296 : ∃ G : SimpleGraph (Fin 127296), BipartiteDD.IsBipartiteDegDiam G 6 9` builds
(`lean/BipartiteDD/Haar/D6D9c/Record127296.lean`). Its own axiom output, `lean/BipartiteDD/Haar/D6D9c/Axioms.out.txt`, is
`'nb_6_9_127296' depends on axioms: [propext, Classical.choice, Quot.sound]`. No `sorry`, `admit`, `native_decide`, or
`axiom` in `lean/BipartiteDD/Haar/D6D9c/`.

## Graph and check

- `python3 research/frontier/build_haar2.py research/frontier/sols/d6D9_sl_17_13_orb3f0_s2.txt`:
  `VALID d=6 D=9 group=sl 17 x Z_13 N=63648 vertices=127296`, ecc 9 from both sides, every vertex reached,
  degree 6, 381888 edges, no duplicate edges.
- Group: SL(2,17) × Z13, order 4896 · 13 = 63648 per side. S: the six elements of the sol file.
- `gen_d6D9c.py` re-checks every A- and B-word of all 63648 elements by direct multiplication before it writes Lean.

## Modules (all in `lean/BipartiteDD/Haar/D6D9c/`)

| Module | Content |
|---|---|
| `SL17.lean` | SL(2,17), numbering `Grp ≃ Fin 4896` (checked by `decide +kernel`); derived from `Haar/SL23.lean` |
| `SL17Z13.lean` | `Grp := SL17.Grp × Multiplicative (ZMod 13)`, `equiv63648 : Grp ≃ Fin 63648` |
| `Check.lean` | S (`sVec`), the A/B words, the packed table reader `codeAt`, checkers `chkA`/`chkB` |
| `Stage00..12.lean` | certificate tables, 4896 indices per stage (13 stages, `63648 = 13 · 4896`), `certA k`, `certB k` by `decide +kernel` |
| `Cover.lean` | `cover1`, `cover2`: every element is an 8-letter A-word / B-word in `SS` |
| `Record127296.lean` | `equiv127296` and `nb_6_9_127296` (via `Diam9`, `haar_isBipartiteDegDiam9_of_equiv`) |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms nb_6_9_127296` |

Generator: `research/lean-haarD/gen_d6D9c.py SOL CODEDIR`. It writes the stage and cover modules into
`lean/BipartiteDD/Haar/D6D9c/` by default. Codes go to `CODEDIR/codes.json`, which is not committed.

## Build record

Built one module at a time, serially, with `lake build <Module>` (and `lake env lean` for Axioms):

- SL17: 26 s. SL17Z13: 2 s. Check (with Diam9): 2 s.
- Stage00: 196 s. Stage01–12: 3–3.5 min each, run by a serial driver script (no parallel builds).
- Cover: 4 s. Record127296: 3 s. Axioms: a few seconds.

The largest stage that built is the whole chain, Stage00–12, then Cover and Record127296.

Memory: `free` showed about 1–2 GB used during stage builds, with no OOM. The D6D9 record needed 2.3–3.5 GB peaks,
so this one is lighter. Per-stage peaks were not measured.

## Obstacles met

None blocking. The cover argument did not hit the `isDefEq` timeout from BRIEF: `cover1` and `cover2` state the cover
against the concrete `SL17Z13.Grp` instances (as in D6D9), and `Record127296` elaborates directly.

## Environment note (for later workers)

`lake` was not installed on this machine, and no `.lake` directory existed. The fix that worked:
`curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.34.1 --no-modify-path`,
then `export PATH=/root/.elan/bin:$PATH`, then `lake exe cache get` (8908 files, about 15 minutes over the proxy).

## Deviations from the brief

- **Branch.** The brief says `lean-haarD-d6D9c`. This session's designated branch is
  `claude/nb-6-9-127296-lean-8oo4po`, and all work is pushed there.
- **Location.** New files go under `Haar/D6D9c/` as the job asked, including the record file. Namespace:
  `BipartiteDD.Haar.D6D9c`, with `SL17`/`SL17Z13` as sub-namespaces. No file or theorem name collides with master.
- **Repo-level `lean/Axioms.lean` not regenerated.** It imports about sixteen master modules (Records, Records9592,
  SingerC, GQST, GQ4, ASq, Haar/Record*), none of which is compiled here. Regenerating it means building most of
  the library. The record-local `D6D9c/Axioms.out.txt` gives the required output, as the D6D9 record did. Adding
  the record to the aggregate is a follow-up for someone who has time to build those modules.
- **Not in the default target.** Nothing imports `D6D9c`, so the default `lake build` is unaffected.

## Timing

Start of the Lean work to a built record: about 50 minutes of build time, with the Mathlib cache download (about
15 minutes) and elan install before that.
