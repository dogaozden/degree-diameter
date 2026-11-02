# c1-a5 notes (round 1, deep-108)

Setup: `python3 ../../a5/gens.py 59` gives A5 gens (A_gens 13 7 1 46 16 26 52 44), r = 4 54 7 21, r2 = 19 7 2 7,
t = 13 7 1 46, s = 2 22 40 57 (same as the card). Shell variables are in env.sh (source it: `. ./env.sh`).

pair0 census (info): |G| = 6159600, |L| = |R| = 10, N = 615960, LL orbits 61668, RL orbits 61596,
double cosets by size: c10:61596 (no special orbits, E_s = 0).

## Task 1: exhaustive scanLR of pair0 (done)
Command per chunk (helper chunk.sh, same cq3 command, timeout 100 s, drops a truncated last line first):
  ./chunk.sh pair0.tsv 300 START 13 pair0_cSTART.log   for START = 0..12, rerun each until "done" (2 runs per chunk).
  Each run covers about 3,800-4,700 members in 100 s (about 25 ms per member: connected members also need the B-root).
Result: 61596 lines, 61596 distinct ids (all regular double cosets), file pair0.tsv. Log lines "scanLR done" in pair0_c*.log.
Connected (uBA+uAA <= 300, uBB computed): 13170 members. Disconnected: 48426 (uBA+uAA from 301 to 1.2M, median 790).
Among connected: uBA+uAA min 110, C min 111, p10 163, median 231, p90 290, max 303.
Minimum C = 111 (60 members, all with uBA 110, uAA 0, uBB 1). Check: `member 1 16 26 52 44 1 8 27 40` gives uBA 110 uAA 0 uBB 1 C 111.
10 best (C uBA uAA uBB id z), z = 8 ints (A-matrix 4, Q-matrix 4):
  111 110 0 1 10765 16 26 52 44 1 8 27 40
  111 110 0 1 11079 16 26 52 44 1 13 46 9
  111 110 0 1 11517 16 26 52 44 1 21 12 17
  111 110 0 1 12123 16 26 52 44 1 32 28 12
  111 110 0 1 12574 16 26 52 44 1 40 7 45
  111 110 0 1 12896 16 26 52 44 1 45 34 56
  111 110 0 1 14391 16 26 52 44 2 11 54 32
  111 110 0 1 14576 16 26 52 44 2 15 3 23
  111 110 0 1 14768 16 26 52 44 2 18 18 15
  111 110 0 1 15313 16 26 52 44 2 29 32 22
No member has C = 0. Pair0 is far from a diameter-8 graph (the best still leaves 110 B-side vertices (uBA) unreached from the A root).

## Task 2: other pairs (census by `info`, 308-member sample with scanLR start 0 step 200, via pair.sh; summ.py)
Pair definitions (gens as 8-int elements "A-matrix Q-matrix"); E_s = sum over non-regular L-orbits on B-cosets of exp(-lambda*s/10),
lambda = 5380840/615960 = 8.736 (E_s from the info census; pair0 has none).
  pair0 L=<(r,r),(t,t)> D5, R=<(r,r2),(I,s)> C10      census c10:61596 E_s 0     exhaustive min 111, conn. median 231
  P1   L=pair0 L,   R=<(r,r2),(t,t)> twisted D5       census c5:120 c10:61536    E_s 1.52  sample median 650, sample min conn 115
  P2   L=pair0 L,   R=<(r2,r),(I,s)>                  census c10:61596 E_s 0     1232-sample: conn 254, min 111, conn median 241
  P3   L=<(r,r2),(t,t)>, R=<(r,r),(I,s)>              census c10:61596 E_s 0     1232-sample: conn 271, min 111, median 232;
                                                                                  1209 of 1232 cost triples equal pair0's sample: likely the same family (side swap/automorphism)
  P4   L=<(r,r2),(t,t)>, R=<(r,r2),(I,s)>             census c2:15 c10:61593    E_s 2.61  1232-sample: conn 285, min 95, conn median 224, p10 164
  P6   L=<(I,r),(t,t)>,  R=<(r,r2),(I,s)>             census c10:61596 E_s 0     308-sample: no member with uBA+uAA <= 300 (min 3330)
  P7   L=<(r,I),(t,s)>,  R=<(I,r),(I,s)>              census c10:61596 E_s 0     308-sample: none connected; R has trivial A-part, so
                                                                                  <L, zRz^-1> projects into D5 in A5: disconnected (uBA ~ 5N/6 type)
  P8   L=<(r,r),(t,t)>,  R=<(I,r2),(I,s)>             census c10:61596 E_s 0     308-sample: none connected (same reason as P7)
  P9   L=<(r,r),(I,s)>,  R=<(I,r2),(t,s)>             census c10:61596 E_s 0     308-sample: none connected (min uBA+uAA 4184)
Reading: E_s = 0 is not sufficient. P6 and P9 are connected but far from diameter 8. P4 has E_s 2.6 but the best sampled
C is 95 (member z = 16 26 52 44 5 8 35 9, confirmed by `member`: uBA 94 uAA 0 uBB 1 C 95), so it is scanned exhaustively
(task 3, p4.tsv, chunk_p4.sh START 13 p4_cSTART.log).

## Task 3: exhaustive scan of P4 (done)
Command per chunk: ./chunk_p4.sh START 13 p4_cSTART.log (same cq3 scanLR command as pair0 with L=<(r,r2),(t,t)>, R=<(r,r2),(I,s)>,
  THR 300, start START step 13), chunks 0..12, two runs per chunk. Result: 61593 lines = all regular cosets (61593), file p4.tsv.
Connected: 13890 (pair0: 13170). Min C = 95 (60 members, uBA 94, uAA 0, uBB 1). No member with C < 95; 0 members with C = 0.
Among connected: p10 160, median 227, p90 286; members with C <= 111: 300 (pair0: 60, all at 111).
Population proxy median (uBA+uAA+uBB, uBB=0 if not computed) 572 (pair0: 570).
10 best (C uBA uAA uBB id z), z = 8 ints:
  95 94 0 1 11237 16 26 52 44 1 16 15 5 ... (first 10 by id among C=95: 11237, 12453, 13441, 13674, 14102, 14667, 15021, 15107, 15467, 16048)
  z for 11237 = 16 26 52 44 1 16 15 5 ; 12453 = 16 26 52 44 1 37 51 0 ; 13441 = 16 26 52 44 1 54 36 57 ;
  13674 = 16 26 52 44 1 58 33 27 ; 14102 = 16 26 52 44 2 6 48 56 ; 14667 = 16 26 52 44 2 16 23 37 ;
  15021 = 16 26 52 44 2 23 23 29 ; 15107 = 16 26 52 44 2 24 50 40 ; 15467 = 16 26 52 44 2 31 56 13 ; 16048 = 16 26 52 44 2 41 47 20.
Verified: `member 1 16 26 52 44 5 8 35 9` (P4 gens) gives uBA 94 uAA 0 uBB 1 C 95 (degrees 10 and 10); z 9 2 6 8 also gives C 95.
Exact scan command for P4 (cq3 59 A L R scanLR p4.tsv 300 0 13 with A, L, R expanded):
  ../../cq/cq3 59 2 13 7 1 46 16 26 52 44 2 4 54 7 21 19 7 2 7 13 7 1 46 13 7 1 46 2 4 54 7 21 19 7 2 7 1 0 0 1 2 22 40 57 scanLR p4.tsv 300 START 13

## Summary
Best connected C: pair0 111 (exhaustive), P4 95 (exhaustive). No C = 0 anywhere, so no CLAIM.txt.
Other pairs were not scanned exhaustively; P3 looks like pair0 (sample nearly identical), P2 is pair0-like, P1 has E_s 1.5 and worse sample.
Helper scripts in this folder: env.sh (variables), chunk.sh (pair0 chunks), chunk_p4.sh (P4 chunks), pair.sh (info + 308 sample),
summ.py and summ50.py (summaries). All commands ran under timeout 100 s with nice -n 10. No background processes.
