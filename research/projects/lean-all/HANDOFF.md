# lean-all: handoff

Branch `claude/lean-all-jvj7b0`, draft PR #313. The table in `STATUS.md` is the current state; this note says how
to continue.

## What is proved

Every theorem is `∃ H : SimpleGraph (Fin N), BipartiteDD.IsBipartiteDegDiam H d D` with only the standard axioms
(`lean/BipartiteDD/LeanAll/Axioms.lean`, output in `Axioms.out.txt`). Three methods:

1. **D = 6 cells**: instances of the Theorem D family (`HexagonD.theoremD`), `LeanAll/D6.lean`.
2. **Graphs up to about 35,000 vertices**: orbit BFS in the kernel (`Orbit.lean`, `Orbit2.lean`, generators
   `gen_orbit.py`, `gen_orbit2.py`, automorphisms from nauty via `auts.py`).
3. **Haar graphs** of `SL(2,p) × Z_n`, `PSL(2,p) × Z_n`, `SL(2,p) × Z_n × SL(2,q)`, `PSL(2,p) × Z_n × SL(2,q)` and
   `PSL(2,p) × Z_n × SL(2,8)`: packed batch checks (`Swar.lean`, `HaarSwar.lean`, `HaarSL.lean`, `HaarPSL.lean`,
   `HaarProd.lean`, `GF8.lean`, `HaarGF8.lean`), certificates from `haarcert.c` / `haarcert_prod.c`, Lean files from
   `gen_haarsl.py` / `gen_haarprod.py`.

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

Records of generated cells whose files are not committed: `axioms_big.txt` (written by `axwatch.py`, which watches
the queue log, and by `bigcell.py`), with `cells.txt` and `manifests/` to regenerate the files.

## What is left

- The cells still building or queued (see `STATUS.md`).
- Large SL cells (12,10), (15,9), (16,9), (13,10), (14,10): `bigcell.py CELL QUEUE LOG --need GB --clean` streams
  them through a running `poolq.py` (writes the batch modules a chunk at a time, deletes each source once built,
  and with `--clean` deletes the batch oleans and certificates after the axioms check). The generated sources take
  about 10 bytes per group element per cover and the oleans about 0.8 of that; (14,10) needs about 5.3 GB of oleans
  at once, so free disk first (older cells' batch oleans, `.lake/build/ir`).
- Hexagon D = 7 cells: the hexagon-family project (branch `claude/hexagon-family-blvamb`) has a Lean certificate
  theorem for these constructions; the instances are theirs.
