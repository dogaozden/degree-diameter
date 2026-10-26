# lean-all: handoff

Branch `claude/lean-all-jvj7b0`, draft PR #313. The table in `STATUS.md` is the current state; this note says how
to continue.

## What is proved

38 records without a Lean ✓ are kernel-checked (table in `STATUS.md`; five of them, (5,8) 9,760, (5,9) 29,756,
(9,8) 546,720, (8,9) 1,341,600 and (11,10) 148,729,680, are sols added to `research/frontier/sols` during this
session): 22 with their Lean files committed (`lean/BipartiteDD/LeanAll/Axioms.lean`, output in `Axioms.out.txt`), and 16 large Haar
cells whose generated files are not committed (`axioms_big.txt`; regenerate with `cells.txt`, compare with
`manifests/`). Every
theorem is `∃ H : SimpleGraph (Fin N), BipartiteDD.IsBipartiteDegDiam H d D` with only the standard axioms. Four
methods:

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

- Hexagon D = 7 cells (7,7) … (16,7): not here. The hexagon-family project (branch `claude/hexagon-family-blvamb`)
  has a Lean certificate theorem for those constructions and says the instance checks are too big for the kernel;
  their record values are also changing.
- (15,10) 2,467,618,800, `SL(2,149) × Z373`: building (see `STATUS.md`); `cells.txt` has the command.
- (16,10) 4,220,872,800, `SL(2,151) × Z613` (2.1 billion elements, 22,800 batches of 92,563 slots): planned after
  (15,10) with `gen_haarsl2.py --per 1 --scan2 --blocks --raw --leaf 16384` and `bigcell.py --truncate --clean`.
  Needs a 10.6 GB certificate file (BFS 4.2 GB of memory with `scan2`), about 12 GB of oleans at the end, and an
  estimated 12 hours on 4 cores.
- The 16 generated cells listed in `axioms_big.txt` were built here and their files then deleted (disk). To re-check
  one, run its `cells.txt` command from `lean/`, compare with `manifests/<Cell>.sha256` (`sha256sum -c`), build
  `Defs`, all `Bat*`, the `Cover*` files and `Record` (e.g. with `poolq.py`, or `bigcell.py` for the largest), and
  `#print axioms` the theorem. Budget: about 10,000 slots per second per core for the batch checks; the largest,
  (14,10), took about 5 hours on 4 cores and needs about 5.3 GB of oleans at once.
