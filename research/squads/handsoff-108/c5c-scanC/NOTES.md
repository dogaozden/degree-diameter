# c5c-scanC (handsoff-108): full scan of coset family C

Card: ../cards.md, section "c5c-scanC". Family C: G = PGL(2,181), H = D5 = <diag(1,42), [[0,1],[2,0]]> (nonsquare
reflection), one regular double coset (degree 10), N = 592,956 per side, 2N = 1,185,912 (> 1,176,480).
Code: exh.c, summ.py, validate.py copied from c6b-exhaust (c6b's folder not written). Built here with
`gcc -O3 -march=native` (binary size equals c6b's exh). Driver: run_C.sh. Output: out/ (C_scanA.tsv, C_scanB.tsv).
Cost C = uBA + uAA + uBB (plain vertices, 0 = diameter 8). P = uBA + uAA is a lower bound on C.

## Verdict
- Family C is exhausted. Exact minimum of the full cost over all 59,202 double cosets = 44 plain vertices (2 classes).
  No member has cost below 44, so NO cost-0 member and no record in family C.
- Proof sketch: C >= P = uBA + uAA for every member, min P over all members = 44 (scanA), and the two classes with
  P = 44 have uAA = uBB = 0, so C = 44 exactly.

## Setup check (matches c6b and c5b)
- regular double cosets 59,202 (199 labels in non-regular ones), classes 16,407 (orbit sizes 1: 90, 2: 3,078,
  4: 13,239), self-inverse double cosets 3,168 (in 1,629 self-inverse classes), normaliser in PGL 20.

## Validation
- validate.py C 100: all 100 first candidates of c5b's C output reproduce uBA, uAA, uBB exactly (100 of 100 OK,
  out/validate_C100.txt). Covers nonzero uAA (cands 1, 3, 8) and nonzero uBB (cands 3, 8).
- The two best classes re-run in member mode give the same numbers as the scan (44, 44; cand z 2 7 167 133 gives 405).

## Full distribution (all 59,202 members = 16,407 classes)
- Lower bound P = uBA + uAA over all members: min 44, p0.1 78, p1 124, p10 211, median 457.
  Members with P <= 50: 8; <= 100: 192; <= 150: 1,432; <= 200: 4,992; <= 300: 16,060; <= 400: 25,848.
- Classes with uAA > 0: 2,636. Classes with P = 0: none.
- Exact full C (all self-inverse classes: C = uBA + 2 uAA; all other classes with P <= 523: B-root pass):
  members with exact C <= 44: 8; <= 50: 8; <= 63: 24; <= 71: 40; <= 100: 192; <= 150: 1,432; <= 200: 4,992;
  <= 300: 16,056; <= 400: 25,848; <= 523: 32,544. The other 23,506 members have C >= P > 523.
- Self-inverse members (3,168): exact C min 405, median 1,726 (much worse than the rest; same effect as in K).
- B-root pass lines (8,144 classes incl. self-inverse): uBB = 0 for 7,920; uBB > 0 for 224 (max 3 plain).

## Top 10 classes (exact full C, plain vertices; the global top 10 because every class with C <= 71 has P <= 71 <= 523
and was B-root computed)
| rank | C | orbit | class id | uBA uAA uBB | z (A-root, normalised) |
|---|---|---|---|---|---|
| 1 | 44 | 4 | 22786 | 44 0 0 | (3, 3, 24, 145) |
| 2 | 44 | 4 | 37938 | 44 0 0 | (6, 3, 72, 157) |
| 3 | 63 | 4 | 850 | 63 0 0 | (1, 3, 29, 88) |
| 4 | 63 | 4 | 15017 | 63 0 0 | (2, 10, 49, 155) |
| 5 | 63 | 4 | 22795 | 63 0 0 | (3, 3, 29, 150) |
| 6 | 63 | 4 | 30885 | 63 0 0 | (5, 2, 52, 166) |
| 7 | 65 | 4 | 5011 | 65 0 0 | (1, 15, 176, 108) |
| 8 | 65 | 4 | 57473 | 65 0 0 | (15, 21, 75, 93) |
| 9 | 71 | 4 | 24877 | 71 0 0 | (3, 10, 114, 79) |
| 10 | 71 | 4 | 51141 | 71 0 0 | (10, 2, 167, 124) |

## Scope notes
- The card's B pass (P <= 50) covered only 2 classes. Its top-10 report was not exact, so the B pass was extended to
  all classes with P <= 523 (the 10th best exact value at that point). That is outside the card's threshold, and it
  was run only for the top-10 report. Log: out/C_scanB.log; file out/C_scanA_top10.tsv (sorted by P).
- No cost-0 class, so no records/ file and no CLAIM line.

## Timing
- scanA: 3,005 s wall for 16,407 classes (about 0.18 s per A-root BFS under load 7-8, nice 10, one process).
- scanB (extension): about 2,700 s for 8,142 classes (two BFS each in scanB code; uBB only is needed).

## Status
- Finished 02:13 UTC. No processes left. Family C is done; the next family-C idea would have no new members to test.
