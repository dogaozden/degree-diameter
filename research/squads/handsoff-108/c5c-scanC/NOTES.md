# c5c-scanC (handsoff-108): full scan of coset family C

Card: ../cards.md, section "c5c-scanC". Family C: G = PGL(2,181), H = D5 = <diag(1,42), [[0,1],[2,0]]> (nonsquare
reflection), one regular double coset (degree 10), N = 592,956 per side, 2N = 1,185,912 (> 1,176,480).
Code: exh.c, summ.py, validate.py copied from c6b-exhaust (c6b's folder not written). Built here with
`gcc -O3 -march=native` (binary size equals c6b's exh). Driver: run_C.sh. Output: out/ (C_scanA.tsv, C_scanB.tsv).
Cost C = uBA + uAA + uBB (plain vertices, 0 = diameter 8). P = uBA + uAA is a lower bound on C, so any class
with P = 44 or more has C >= 44, and a cost-0 member needs P = 0.

## Setup check (matches c6b and c5b)
- regular double cosets 59,202 (199 labels in non-regular ones), classes 16,407 (orbit sizes 1: 90, 2: 3,078,
  4: 13,239), self-inverse double cosets 3,168 (in 1,629 self-inverse classes), normaliser in PGL 20.

## Validation
- validate.py C 100: all 100 first candidates of c5b's C output reproduce uBA, uAA, uBB exactly (100 of 100 OK,
  out/validate_C100.txt). Covers nonzero uAA (cands 1, 3, 8) and nonzero uBB (cands 3, 8).
- The two best classes re-run in member mode (ids 22786, 37938) give the same numbers as the scan.

## Results: scanA (A-root, all 16,407 classes; 3,005 s wall, nice 10, one process)
- P = uBA + uAA over all 59,202 members: min 44, p0.1 78, p1 124, p10 211, median 457.
  Members with P <= 50: 8; <= 100: 192; <= 150: 1,432; <= 200: 4,992; <= 300: 16,060.
- Classes with uAA > 0: 2,636. Classes with P = 0: none.

## Results: scanB (B-root)
- The card's B pass (P <= 50) covers 2 classes: ids 22786 and 37938 (orbit 4 each), both uBA 44, uAA 0, uBB 0.
  So exact full C = 44 for 8 members. Since C >= P >= 44 for every member, this is the exact family minimum:
  NO member of family C has cost below 44, and none has cost 0.
- Self-inverse classes (exact C = uBA + 2 uAA, no B pass needed): min 405 (id 14279), median 1,726, 10 members <= 500.
  Self-inverse members are much worse than the rest (c5b measured the same for K).

## Top 10 (exact)
- The 10th best exact value (523) is above 50, so the card's P <= 50 rule does not settle the top 10: a
  non-self-inverse class with 50 < P <= 523 could still beat them. That is 8,144 classes minus the 2 done.
- Extension (beyond the card's threshold, run only to make the top-10 report exact): B-root pass for all classes with
  P <= 523 (out/C_scanA_top10.tsv, sorted by P, same scanB code, THR 523). Log: out/C_scanB.log.
  It does not change the conclusion (min 44 is already exact); it only settles ranks 3-10.

## Status
- scanA complete (16,407 of 16,407 classes) at 01:22 UTC; B pass for P <= 50 done (2 classes, 01:22 UTC).
- B pass extension to P <= 523 started 01:24 UTC.
