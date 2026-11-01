# c5c-scanC (handsoff-108): full scan of coset family C

Card: ../cards.md, section "c5c-scanC". Family C: G = PGL(2,181), H = D5 = <diag(1,42), [[0,1],[2,0]]> (nonsquare
reflection), one regular double coset (degree 10), N = 592,956, 2N = 1,185,912 (> 1,176,480).
Code: exh.c, run_all.sh (K/C scanA of c6b; not used here), summ.py, validate.py copied from c6b-exhaust (not edited
there). Built here with `gcc -O3 -march=native` (binary size equals c6b's exh). Driver for this run: run_C.sh.
Cost C = uBA + uAA + uBB (plain vertices, 0 = diameter 8). P = uBA + uAA is a lower bound on C.
A cost-0 member needs P = 0, so only P = 0 classes can be records; the B pass is for ranking.

## Setup check (matches c6b)
- regular double cosets 59,202 (199 labels in non-regular ones), classes 16,407, self-inverse double cosets 3,168,
  normaliser in PGL 20. Same as c6b's and c5b's counts.

## Validation
- validate.py C 100: all 100 first candidates of c5b's C output (C_pgl181_D5_10_nsq.out) reproduce uBA, uAA, uBB
  exactly (100 of 100 OK; out/validate_C100.txt). Covers nonzero uAA (cand 1, 3, 8) and nonzero uBB (cand 3, 8).

## Run plan
- scanA: all 16,407 classes, A-root BFS (about 0.13 CPU-s each), nohup, nice -n 10, resumable (out/C_scanA.tsv).
- scanB: uBB for classes with P <= 50, in increasing P order (out/C_scanA_best.tsv), out/C_scanB.tsv.
- summ.py C -> distribution and top-10 classes.

## Status
- started scanA at 00:30 UTC (run_C.sh, pid in ps). 
