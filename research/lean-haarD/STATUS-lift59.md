# STATUS lift59: Δ5·D9 on 28,560 vertices in Lean

**Done.** `nb_5_9_28560 : ∃ G : SimpleGraph (Fin 28560), BipartiteDD.IsBipartiteDegDiam G 5 9` builds
(`lean/BipartiteDD/Haar/LiftB/Record.lean`). Its axioms, from `lean/BipartiteDD/Haar/LiftB/Axioms.out.txt`:

    'nb_5_9_28560' depends on axioms: [propext, Classical.choice, Quot.sound]

No `sorry`, `admit`, `native_decide` or `axiom` in `lean/BipartiteDD/Haar/LiftB/`. The certificates use `decide +kernel` only.

## Graph and check

- Group: `Z_595 ⋊ Z_24`, `(a,j)(b,l) = (a + 53^j b, j + l)`, order 14280 per side, so 28560 vertices. S is the five
  elements `(0,0) (556,1) (172,11) (75,23) (170,5)` of `research/lifts/sols/d5D9_n28560_haar_meta595_24_53.txt`. The
  haar_gen3 copy `research/lifts/sols/haar/hc_d5D9_meta_595_24_53_1_s1.txt` lists the same S, and the generator asserts this.
- Coordinator tools, rerun here: `python3 build.py meta 595 24 53 0,0 556,1 172,11 75,23 170,5` gives n=28560,
  71400 edges, degree 5, bipartite, and `apsp` reports `RESULT VALID d=5 D=9 n=28560`.
- `research/lean-haarD/gen_lift59.py` re-checks, by direct sequential multiplication, every A-word and B-word of all 14280
  elements (eight letters, alternating as in `Haar/Diam9.lean`) before it writes Lean. It found covers for both sides.

## Modules (all in `lean/BipartiteDD/Haar/LiftB/`)

| Module | Content |
|---|---|
| `Meta595.lean` | `Z_595 ⋊ Z_24` as a `Group`, numbering `Grp ≃ Fin 14280`. Copied from the `Meta279` pattern of `D6D7/Group.lean`. |
| `Check.lean` | S (`sVec`), `wordA`/`wordB`, packed table reader `codeAt` (19 bits per code, `5^8 < 2^19`), checkers `chkA`/`chkB`. Generated. |
| `Stage00.lean` … `Stage09.lean` | Certificate tables, 1428 indices per stage (10 stages), `certA k` and `certB k` by `decide +kernel`. Generated. |
| `Cover.lean` | `exA`, `exB`, `cover1`, `cover2`: every element is an eight-letter A-word and B-word in `SS`. Generated. |
| `Record.lean` | `equiv28560` and `nb_5_9_28560`, via `haar_isBipartiteDegDiam9_of_equiv`. |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms nb_5_9_28560`. |

Generator: `python3 research/lean-haarD/gen_lift59.py SOL HAAR CODEDIR [LEANDIR]`. Codes go to `CODEDIR/codes.json`,
which is not committed.

## Build record

Serial, one module per `lake build` (or `lake env lean` for Axioms), Mathlib cache fetched first (8908 files):

- Meta595: 3.3 s. Check: 2.0 s. Stage00: 21 s. Stage01–09: 21–23 s each, run in a serial loop.
- Cover: 2.8 s. Record: 1.3 s, plus about 9 s for the master modules it imports (Basic, Graph, GraphD, Main, Diam9), which
  were not yet built on this machine.
- Axioms: 2.7 s.

The largest stage that built is the whole chain: Stage00–09, Cover, Record and Axioms. Nothing was blocked.

## Deviations from the brief

- **Branch.** The brief says `lean-haarD-lift59`. The session's designated branch is `claude/lift59-nb-5-9-28560-t6yze3`,
  and all work is pushed there.
- **Repo-level `lean/Axioms.lean` not appended or regenerated.** Doing so would mean building roughly ninety unrelated
  library modules, which the brief's build-only-what-you-touch rule rules out. The record-local `LiftB/Axioms.out.txt`
  gives the required output, as the D6D9c record did. Adding the record to the aggregate is a follow-up.
- **Commit attribution.** The commit's co-author line is `Claude <noreply@anthropic.com>`, without the model name, because
  the session's rule against model identifiers in pushed artifacts takes precedence over the attribution reminder.
- **Not in the default target.** Nothing imports `LiftB`, so the default `lake build` is unaffected.

## Obstacles met

None blocking. `isDefEq` on the cover argument did not occur: `cover1` and `cover2` state the cover against the concrete
`Meta595.Grp`, as in D6D9c, and `Record` elaborates directly.
