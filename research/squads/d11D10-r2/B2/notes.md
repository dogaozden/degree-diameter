# B2: speed of one k = 10 RANDORB sample (psl 243 x Z11)

Status: sweep queued at the gate (12:57). Results below are filled in when the sweep log is complete.

## Code
- haar_sym_B2.c = research/structured/haar_sym.c plus three changes (all cost-neutral):
  1. ORBPROF=1 times the phases of each RANDORB sample (random_orbit, mktab calls, cost_any) and the BFS levels (TIMING).
  2. SEQ=1 prints every sample cost; a seqhash over the cost sequence is printed per variant.
  3. PFDLIST="p1 p2 ..." reruns the same samples (same RNG state) once per prefetch distance PFD.
  4. HUGEPG=1 allocates the big random-access tables (POS, POSW, IDXK, zero_s, F/Fn/V/NB bitsets) with 2 MB alignment and
     madvise(MADV_HUGEPAGE). THP is in "madvise" mode on this machine.
- Build: gcc -O3 -march=native -fopenmp -o haar_sym_B2 haar_sym_B2.c -lm (binary haar_sym_B2 in this folder).

## Commands (sweep.sh, one gate slot, run back to back)
    gate.sh 330 bash B2/sweep.sh
  P1  env -u THREADS ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=30 ORBPROF=1 SEQ=1 PFDLIST="8 0 4 16 32" FAST=2 haar_sym_B2 11 10 600 5 8 /dev/null psl 243 11
  P3  same with PFDLIST="8 16" HUGEPG=1 FAST=2
  P2  same with FAST=1 (narrow rows)
  P4  original research/structured/haar_sym, same parameters, FAST=2 (cost check against P1)
