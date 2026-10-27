# lean-all: handoff

Branch `claude/lean-all-jvj7b0`, draft PR #313. The table in `STATUS.md` is the current state; this note says how
to continue.

## What is proved

57 records without a Lean ✓ are kernel-checked (table in `STATUS.md`, 61 rows marked done; four of those records were
later raised and the new values are checked too). Seven of them, (5,8) 9,760, (5,9) 29,756, (9,8) 546,720, (8,9)
1,341,600, (11,10) 148,729,680, (15,10) 2,467,618,800 and (16,10) 4,220,872,800, are sols added to
`research/frontier/sols` during this session, and 14 are records outside the README table (research/RESULTS.md).
35 have their Lean files committed (`lean/BipartiteDD/LeanAll/Axioms.lean`, output in `Axioms.out.txt`); 26 large
cells have generated files that are not committed (`axioms_big.txt`; regenerate with `cells.txt`, compare with
`manifests/`). Every theorem is `∃ H : SimpleGraph (Fin N), BipartiteDD.IsBipartiteDegDiam H d D` with only the
standard axioms. Six methods:

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

- Hexagon D = 7: (15,7) has seven levels H H D H H D D, three matchings, and frees collinear pairs on the friendly
  transitions (research/d15D7b/RELAXED.md: each pair is served by two hubs, so some main-main routes go through hubs).
  It needs a seven-level theorem with that rule; `Route`/`RouteHub` assume main-main routes inside the levels.
- The 18 generated cells listed in `axioms_big.txt` were built here and their files then deleted (disk). To re-check
  one, run its `cells.txt` command from `lean/`, compare with `manifests/<Cell>.sha256` (`sha256sum -c`), build
  `Defs`, all `Bat*`, the `Cover*` files and `Record` (e.g. with `poolq.py`, or `bigcell.py` for the largest), and
  `#print axioms` the theorem. Budget: with `gen_haarsl.py` about 10,000 slots per second per core ((14,10) took about
  5 hours on 4 cores, 5.3 GB of oleans at once); with `gen_haarsl2.py`, (15,10) took 6.4 hours and (16,10) 13.2
  hours (12 GB of oleans at once).
- A cover module that imports more than about 10,000 batch modules spends a long time after writing its `.olean` on
  the `.ilean` (Lean's reference search maps over the array of all imported module names for every identifier, so
  the cost is quadratic): for (16,10) the `.olean` was written about a minute after the imports loaded and the
  `.ilean` was still running 20 minutes later. Build such covers (and the Record) without `-i`; the `.ilean` is only
  for the editor.
- After a restart of the machine the disk is slow to read (about 2-5 MB/s for one reader, 60-100 MB/s with 16
  parallel readers): warm the oleans with parallel `cat` before importing thousands of them.
