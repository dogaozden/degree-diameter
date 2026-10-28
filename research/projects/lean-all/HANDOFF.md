# lean-all: handoff

Branch `claude/lean-all-jvj7b0`, draft PR #313. The table in `STATUS.md` is the current state; this note says how
to continue.

## What is proved

Every row of the README table without a Lean ✓ (49 of its 74 rows on master, 2026-10-27) is kernel-checked at the
README's value, and so are 16 records outside the table (research/RESULTS.md, research/frontier/beyond). Six more
rows of `STATUS.md` are other values of README cells, also checked: larger graphs from research/frontier/sols or
RESULTS.md ((5,9) 29,756, (7,10) 2,298,240, (8,10) 8,043,840, (9,8) 546,720) and values since raised ((8,9)
1,326,960, (13,5) 11,486). That makes 71 rows, all done. 37 have their Lean files committed
(`lean/BipartiteDD/LeanAll/Axioms.lean`, output in `Axioms.out.txt`); 34 large cells have generated files that are
not committed (`axioms_big.txt`; regenerate with `cells.txt`, compare with `manifests/`). Every theorem is
`∃ H : SimpleGraph (Fin N), BipartiteDD.IsBipartiteDegDiam H d D` with only the standard axioms. Eight methods:

1. **D = 6 cells**: instances of the Theorem D family (`HexagonD.theoremD`), `LeanAll/D6.lean`.
2. **Graphs up to about 35,000 vertices**: orbit BFS in the kernel (`Orbit.lean`, `Orbit2.lean`, generators
   `gen_orbit.py`, `gen_orbit2.py`, automorphisms from nauty via `auts.py`).
3. **Haar graphs** of `SL(2,p) × Z_n`, `PSL(2,p) × Z_n`, `SL(2,p) × Z_n × SL(2,q)`, `PSL(2,p) × Z_n × SL(2,q)` and
   `PSL(2,p) × Z_n × SL(2,8)`: packed batch checks (`Swar.lean`, `HaarSwar.lean`, `HaarSL.lean`, `HaarPSL.lean`,
   `HaarProd.lean`, `GF8.lean`, `HaarGF8.lean`), certificates from `haarcert.c` / `haarcert_prod.c`, Lean files from
   `gen_haarsl.py` / `gen_haarprod.py`. `SL(2,16) × Z_n` (`GF16.lean`, `HaarGF16.lean`, `gen_haar16.py`): one batch
   per element of `SL(2,16)` and free entry, the `n` slots are the `Z_n` part, checked by the `HaarSwar` batch over
   `ZMod 2` with identity letters. `SL(2,25) × Z_n` the same way over `GF(25) = F₅[x]/(x² + 2)` (`GF25.lean`,
   `HaarGF25.lean`, `gen_haar25.py`).
4. **Small metacyclic Haar graphs** `Z_m ⋊_r Z_k` (`gen_meta.py`): one word per element, checked in stage tables.
5. **Hexagon D = 7 cells with three levels** ((7,7), (9,7), (10,7), (13,7)): Theorem 1 of the hexagon-family project
   (`HexagonD7`, copied unchanged) with its hypotheses reduced to local certificates (`HexArith.lean`, `HexLocal.lean`
   over `ZMod p`; `HexGen.lean` over any field through a `Coder`, `HexGF8.lean` for GF(8)). A point is a normalised
   base-p code, a line a normalised basis with Plücker coordinates; the points and lines near the freed set R are
   listed with their incidences, completeness comes from counting (`mem_of_card`), sigma is extended to a bijection
   (`exists_equiv_extend`), and the hub graph is checked by Orbit2 BFS. `hexlocal.py SOL HEXBIN OUT.json` writes the
   certificate, `gen_hexcell.py OUT.json NAME OUTDIR --theorem THM` the cell.
6. **Typed levels** (research/squads/cells/d16D7.md): `Typed.lean` proves the typed-levels theorem over any
   generalized hexagon (levels of type H or its dual, two matchings per level, identity on friendly transitions,
   `swapE τ` with a local duality on the others, hubs in the free slots); `TypedHex.lean` gets the friendly freed sets
   from global tables, `VHub.lean` takes hub graphs that are Z_m voltage graphs, and `TypedHex5.main5` is the
   five-level instance over `ZMod p` (degree p + 3). `gen_typedcell.py HEXBIN TYPED_SOL VHUB NAME OUTDIR --lc CELL ...`
   writes a cell that reuses the local certificate of a three-level cell (TypD14D7 uses HexD13D7's).
7. **Freed spreads with a duality** ((11,7), (12,7), research/squads/cells/d12D7.md): `Route.lean` is `Typed` with a
   route hypothesis in place of (H1)/(H3); `Spread.lean` proves the route for the points of pairwise opposite lines
   freed on every transition with a duality as every matching (`via_all`: along a shortest walk some point is not
   freed, or a non-freed point is found next to it); `GF9.lean`/`HexGF9.lean` give GF(9) and its coder;
   `HexGlobal.lean` tables all points and lines of H(q), checks the duality flag by flag (both directions by
   counting) and the spread flags. `SpreadHub.lean` adds cluster-assisted hubs: same-side hub distances through an
   auxiliary graph (hubs, owners, spread lines and their dual images) mapped into the graph edge by edge, searched
   from one hub of each kind and spread by its automorphisms (nauty). Generators `gen_spreadcell.py` (voltage hub
   graph) and `gen_spreadhub.py` (hubs of a .hubs3 file); `--stub` writes empty data and `sorry` checks to test a
   Record before the build.
8. **Seven typed levels with relaxed friendly sets** ((15,7), research/d15D7b/RELAXED.md): `RTyped.lean` is `Typed`
   with friendly sets whose elements may have one co-adjacent partner, each pair served by two hubs whose other slots
   are incident with the partner (`r1`, `r1h`). `Relax7.main7` is the seven-level instance over `ZMod p`: every
   element is a code (`den`), transition `a → a + k` is number `3a + k - 1`, the slot lists of a level are the three
   freed (or image) lists, the hubs hold explicit positions (`tA`, `tB`, injective by inverse tables), and the hub
   graph is any bipartite graph given by neighbour lists whose same-side distances are at most 6 by itself, checked by
   layered bit sets (`BitBFS.reach6`: layers 2 to 5 of a search from all of one side at once are data, each checked
   against the layer before it with 8 lookups per vertex). `Relax7Chk` has the Bool checks: `ph2OK`/`lh2OK` (freed
   points or lines with partners: every table line has one or two owners, all in {r, pr r}), `hubChk` (the two hubs
   of a pair), `local_duality'`. The record's own hub graph needs the levels for 1,403 same-side pairs, so the cell
   uses `sols/d15D7_hub_10826_10481.txt` (degree-preserving swaps from it, `tools/opt.c`). Generator
   `gen_relax7.py HEXBIN SOL HUB LCJSON NAME OUTDIR --theorem THM` (LCJSON: `hexlocal.py` of the d13D7 mirror .sol,
   checked equal to the mirrored set of the (15,7) .sol); kernel cost measured: about 8 ms per vertex and layer.

## How to build a Haar cell

From `lean/`:

```
gcc -O2 -o /tmp/claude-0/work/haarcert ../research/projects/lean-all/haarcert.c
gcc -O2 -o /tmp/claude-0/work/haarcert_prod ../research/projects/lean-all/haarcert_prod.c
python3 ../research/projects/lean-all/gen_haarsl.py SOL OUTDIR MODULE THEOREM --per K   # see cells.txt
```

Then build `Defs`, all `Bat*`, the `Cover*` files and `Record` (in that order; the `Bat*` modules are independent).
`poolq.py QUEUE LOG BUDGET_GB MAXJOBS` runs a queue file of `MOD:GB` lines with `--` barriers between the stages and
a memory budget; `!MOD:GB` runs `lean` directly (no lake start-up). A batch module of about 0.5 MB peaks near 2.7 GB.
Check the result with `#print axioms` (add the cell to `Axioms.lean`).

Things that cost time here, now avoided by the generators:

- a long hex literal costs time quadratic in its length to elaborate: the certificates are written as balanced trees of
  4,096-bit literals joined by `+` and `<<<` (`chunked`), about 5× faster than one literal per batch;
- `omega` on a many-way case split is very slow and leaves large proof terms: ranges are joined by
  `range_join`/`range_one` (`LeanAll/Range.lean`) in balanced trees;
- editing an imported library file (`HaarSL.lean`, `HaarPSL.lean`, …) makes lake rebuild every generated module above
  it; add new lemmas in new files.
- for large SL cells use `gen_haarsl2.py` (same options): its batch modules import only `Core/HaarCore.lean` (no
  Mathlib), which saves about 2.4 s of Lean start-up per module, and with `--raw --leaf 16384` the certificate trees
  are raw literals (`Nat.add`/`Nat.shiftLeft`), about 3× faster to elaborate and 5.6 instead of 8.1 bytes of olean per
  slot. Measured on (15,10) under 4 jobs: 9.5 s per batch with `gen_haarsl.py --per 1`, about 4 s with
  `gen_haarsl2.py --per 2 --raw --leaf 16384`. Memory grows by about 1.1 GB per (55,577-slot) batch in a module and is
  only released at the end of the module, so keep `--per` small for big batches;
- `haarcert ... scan2` needs 2 bytes per element instead of 6 (same words as `scan`), and `scan2 FROM TO` writes only
  the words of the elements `FROM <= k < TO` (used to restore the cut tail of a certificate file);
- `bigcell.py --truncate` writes the chunks from the last one down and cuts the certificate file below each written
  chunk, so the certificate shrinks while the oleans grow (disk); chunks whose oleans exist are skipped on a restart.

Records of generated cells whose files are not committed: `axioms_big.txt` (written by `axwatch.py`, which watches
the queue log, and by `bigcell.py`), with `cells.txt` and `manifests/` to regenerate the files.

## What is left

- Nothing in the README table: all 49 rows without ✓ are checked. A record added to README.md or RESULTS.md later
  needs a cell: pick the method by construction (list above), copy the nearest `cells.txt` line, build with
  `topobuild.py` (orbit, hexagon, typed and relaxed cells) or `poolq.py`/`bigcell.py` (Haar cells), `#print axioms`
  the theorem and add a row to `STATUS.md`.
- Memory: the cgroup limit is about 14.3 GB including page cache, and generated cells map their data oleans (3 GB for
  SpreadD11D7). The OOM killer then kills the largest lean process (rc=-9 in the topobuild log). Seen here: GLn of
  SpreadD11D7 (3 GB anonymous, 6 GB mapped) next to two other jobs; TypD16D7's HLoc modules with 4,096 hub vertices
  per theorem (fixed with `gen_typedcell.py --hchunk 1024`); RelaxD15D7's Cg modules (4 GB); the step modules of
  orbit cells above about 40,000 vertices (fixed with `gen_orbit2.py --staged --schunk 16384`, which splits each
  step module of a stage into parts of 16,384 vertices; D20D5, D18D5 and D19D5 use it). Run one heavy module at a
  time: `ONLY='P_' topobuild.py DIR 3` builds the light data modules first, then `SKIP_BUILT=1 topobuild.py DIR 1`
  the rest. Generating a large orbit cell (`gen_orbit2.py` on 50,000 vertices) needs several GB too: do not run it
  next to a Lean build.
- The generated cells listed in `axioms_big.txt` were built here and their files then deleted (disk). To re-check
  one, run its `cells.txt` command from `lean/`, compare with `manifests/<Cell>.sha256` (`sha256sum -c`), build it
  (`topobuild.py`, or for Haar cells `Defs`, all `Bat*`, the `Cover*` files and `Record`, e.g. with `poolq.py`, or
  `bigcell.py` for the largest), and `#print axioms` the theorem. Budget: with `gen_haarsl.py` about 10,000 slots per
  second per core ((14,10) took about 5 hours on 4 cores, 5.3 GB of oleans at once); with `gen_haarsl2.py`, (15,10)
  took 6.4 hours and (16,10) 13.2 hours (12 GB of oleans at once). Staged orbit cells cost most in their middle
  stages (D19D5: about 100 s per step module in the first and last stages, up to 1,800 s in the third).
- A cover module that imports more than about 10,000 batch modules spends a long time after writing its `.olean` on
  the `.ilean` (Lean's reference search maps over the array of all imported module names for every identifier, so
  the cost is quadratic): for (16,10) the `.olean` was written about a minute after the imports loaded and the
  `.ilean` was still running 20 minutes later. Build such covers (and the Record) without `-i`; the `.ilean` is only
  for the editor.
- After a restart of the machine the disk is slow to read (about 2-5 MB/s for one reader, 60-100 MB/s with 16
  parallel readers): warm the oleans with parallel `cat` before importing thousands of them
  (`find .lake/build/lib/lean/BipartiteDD/LeanAll/CELL -name '*.olean' | xargs -P 16 -n 50 cat > /dev/null`). The page
  cache is also dropped from time to time during long builds (iowait goes up, a module takes 2-5× longer): re-read
  the cell's and Mathlib's oleans every few minutes while it runs.
- Worker restarts kill background jobs but keep `/tmp` and the oleans: resume with `SKIP_BUILT=1 topobuild.py DIR 1`.
