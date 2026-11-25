# Files for Section 7 of SYNTHETIC.tex

Copies of solution files and edge lists that are not on `master` (taken from the beyond branches), and the logs of
the second checks run for the note (marked ′ in Appendix B).

## Copied files

- `d4D12_meta_1277_29_964_h08.txt`, `d4D13_meta_2237_43_1984_h03.txt`, `d4D14_meta_2731_91_i04.txt`,
  `d5D13_prodmeta_11_5_2971_11_i06.txt`, `d5D14_meta_148781_43_i07.txt`, and the D = 13, 14 SL/PSL files
  `d6D13_…` to `d10D13_…`, `d6D14_…` to `d8D14_…`: from `research/frontier/beyond13/sols/` on
  `claude/beyond-d13-search-z35z61`.
- `d16D11_psl_449_331_orb3-5-1_s1.txt`: from `research/frontier/sols/` on `claude/beyond-d11-d12-new-cells-3t3djx`.
- `d3D11_n1474_meta67_11_9.edges.gz`: from `research/frontier/beyond/graphs/` on `claude/new-cells-beyond-etos3t`.

## Second checks (`*.haarcheck_sl.txt`, `*.haarcheck_psl*.txt`)

Run on 2026-11-01 in the cloud container of this note's session (4 cores, 15 GB), with the lab's checkers as on
`master` at 9a97f7a5, built with `cc -O3`:

- `*.haarcheck_sl.txt`: `research/frontier/haarcheck_sl.c` (the SL files);
- `*.haarcheck_psl.txt`: `research/structured/tools/haarcheck_psl.c` (the PSL files).

No second check of `d10D13_psl_503_157_orb3-3-1_s1.txt` was run: a full run was killed for lack of memory after
25 s while the other checks ran (the PSL checker used 4.1 GB at N = 5.7e9, so about 7 GB at N = 1.0e10), and two
half runs one after the other would have taken about two more hours.

The first line of each log names both possible sources; the file name says which one ran. Each log records the
sha256 of the solution file it checked, which is the sha256 of the copy in this folder.
