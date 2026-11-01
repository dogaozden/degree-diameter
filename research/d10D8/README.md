# research/d10D8: the (10,8) cell (cell-10-8 session, 2026-10-24)

Notes and results: `../squads/cells/d10D8.md`. Squad rounds: `../squads/d10D8-r1/`, `../squads/d10D8-r2/` and
`../squads/LOG.md`.

## Folders

- `runs/`: logs (`*.log` progress on stderr, `*.out` RESULT line), checkpoints (`*.ckpt`: best set so far, element
  indices as in haar_sym) and solution files (`*.txt`, written only when a run reaches cost 0) of the orbit-symmetric
  Haar searches. Names: `d10D8_<group>_orb3[_variant]_s<seed>`.
- `zopt/haar_zopt.c`: `../structured/haar_sym.c` plus three analysis modes for G = Q × Z_n (n prime), ORBIT="k m 1":
  - `ZOPT=1` (with `CKPT=file`): keep the Q-parts of the set, try every Z_n-offset vector (projective points of
    PG(m−1, n)) and report the best cost and the number of zero-cost points; a zero is checked and written.
  - `ZOPT=r:K`: the same for K random orbit sets; with `ZONLYDUP=1` only the z-independent duplicate statistics
    (`ZCOEF`: distinct coefficient vectors, pairs sharing one, generic duplicate estimate; `ZDUP`: measured
    duplicate rate of each set).
  - `NEIGH=K` (with `CKPT=file`, optional `NTARG=percent`): cost histogram of K single-orbit replacements of the set.
  Build: `gcc -O3 -march=native -fopenmp -o haar_zopt haar_zopt.c -lm`. Example:
  `ORBIT="3 3 1" CKPT=../runs/X.ckpt ZOPT=1 ./haar_zopt 10 8 1 1 8 out.txt psl 23 97`.
- `sym2/haar_sym2.c`: `../structured/haar_sym.c` plus `RESTARTAFTER=r` (reheat from the best set of the current
  chain; after r reheats in a row without improving it, start a fresh chain from random orbits; the global best is
  kept for the output file and the checkpoint). Unset, it behaves exactly like haar_sym. Second session additions:
  - `RESTARTAFTER=0`: every stall starts a fresh chain; each finished chain prints
    `CHAIN n min <cost or ORBW energy> secs <s> evals <e> S <10 element indices>`.
  - `INVPAIR=1`: S = {e} ∪ O ∪ O⁻¹ ∪ (α-orbit of involutions); `INVPAIR=2`: S = {e} ∪ O ∪ β(O)⁻¹ ∪ (α-orbit of
    elements with β(x) = x⁻¹), β an outer involution of the first factor of a prod group commuting with α (both
    negative, cell notes §8.2 and §8.4).
  - `EXDESC=1`: exhaustive best-response descent over all α-orbits per slot (cell notes §8.3).
  - `F0=i`: the α-fixed letter is the i-th non-identity fixed element instead of e (no effect, §8.5).
- `launch.sh TAG SEED "GROUP" [VAR=x ...]`: starts one ORBIT="3 3 1" run in runs/ (resumable through runs/TAG.ckpt),
  e.g. `./launch.sh d10D8_psl_23_97_orb3_F15W3_s61 61 "psl 23 97" RESTARTAFTER=0 COOL=15 REHEAT=30 ORBW=3`.
- `hex/`: hexagon tools copied from the cell-10-7 branch (`hexgen2.c` builds H(q), `hexcheck.c`, `lift2.c` the lift
  annealer) and `lift3.c` = lift2.c plus `HSUB=b` (hexagon voltages restricted to the element indices 0, b, 2b, …).
  `./hexgen2 q` writes `hex/hex_q{q}.bin`; then e.g. `HZERO=1 MCONST=1 GROUP="cyc 10" T="1 4" J=2 D=8 ITERS=0 ./lift3 3`
  checks the ten-level lemma of the cell notes.

## Checking a solution

Haar graphs: `python3 ../frontier/build_haar2.py runs/<file>.txt` and `python3 ../frontier/check_haar_indep.py
runs/<file>.txt` (two independent implementations; both build the group from its definition).
