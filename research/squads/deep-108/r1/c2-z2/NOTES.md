# c2-z2 notes (PSL(2,181) x Z2, cq2; |G| = 5,929,560, N = 592,956, lambda = 5380840/N = 9.07)

Generators (cq2 format "a b c d res", res mod 2), checked by hand (python, this folder):
- x  = "1 0 0 42 0"  diag, order 5 in PSL (scaled to det 1: 46 0 0 122)
- t0 = "0 1 180 0 0" involution inverting x (the card's y); its class: b = 1 (square)
- w2 = "0 2 90 0 0"  involution inverting x, b = 2 (2 is a non-square mod 181, 2^90 = -1)
- c10 = "1 0 0 139 0" order 10 in PSL (scaled 31 0 0 146)
Extra check: N_PSL(<x>) = D_180 and conjugation by r (r t0 r^-1 = r^2 t0) shifts the reflection index by 2, so the
D5s containing <x> form TWO PSL-classes (b square / b non-square). The card lists only the square one (t0). The
non-square one (w2) is added below as classes D5o / D5ot.

Classes (order-10 subgroups of PSL x Z2 with trivial kernel to PSL, up to conjugacy; (I,1)-containing ones skipped):
- D5e  = <(x,0),(t0,0)>  card's D5x0          gens: "2 1 0 0 42 0 0 1 180 0 0"
- D5et = <(x,0),(t0,1)>  card's D5'           gens: "2 1 0 0 42 0 0 1 180 0 1"
- D5o  = <(x,0),(w2,0)>  NOT in the card      gens: "2 1 0 0 42 0 0 2 90 0 0"
- D5ot = <(x,0),(w2,1)>  NOT in the card      gens: "2 1 0 0 42 0 0 2 90 0 1"
- C10  = <(c10,0)>       card's C10x0        gens: "1 1 0 0 139 0"
- C10t = <(c10,1)>       card's C10'         gens: "1 1 0 0 139 1"

Commands are logged below as they run.

- Residue argument (checked): if L and R are both untwisted (all elements res 0, or all of L res 0 and R res 0), every
  double coset L z R has constant residue, so the bi-coset graph splits into two components. Seen directly:
  D5e x D5e member z = (1,0,1,1,0): uBA 297303 uAA 296478 (half the graph unreached). So untwisted x untwisted pairs
  are dropped. Twisted subgroups are required for connectivity.

Census (info, L = R or the pair): D5e, D5et, D5o, D5ot all give c1:4 c2:16 c5:176 c10:59204 (E_s 6.10);
C10 and C10t both give c1:36 c10:59292 (E_s 14.53). The card's K had E_s 3.5.

## Pair census and 297-member samples (run_pair.sh; samp_<L>_<R>.tsv, THR 300, index = 0 mod 200)
Notation: D5e = card's D5x0 (t0 untwisted), D5et = card's D5' (t0 twisted), C10 = card's C10x0, C10t = card's C10'.
Extra classes (not in the card): D5o = <(x,0),(w2,0)>, D5ot = <(x,0),(w2,1)> (w2 = "0 2 90 0 0", the non-square
reflection class; the card's list has only the square class, see above).
E_s from the B-orbit census of info (lambda 9.07). medUA = median of uBA+uAA over all 297 members; medC = median of C
over the members with uBB computed (uBA+uAA <= 300); conn = members with uBA+uAA <= 300.

| pair (L, R)          | census (info)               | E_s   | conn | minC | p10C | medC | medUA |
|----------------------|-----------------------------|-------|------|------|------|------|-------|
| D5e x D5e            | c1:4 c2:16 c5:176           | 6.10  | 0    | -    | -    | -    | 592958 (disconnected) |
| D5e x D5et (a)       | c2:18                       | 2.93  | 128  | 72   | 138  | 220  | 343   |
| D5e x D5ot (b)       | c2:18                       | 2.93  | 104  | 68   | 136  | 218  | 379   |
| D5e x C10t (c)       | c2:18                       | 2.93  | 98   | 59   | 149  | 236  | 375   |
| D5et x D5et         | c1:4 c2:16 c5:176           | 6.10  | 77   | 102  | 166  | 246  | 444   |
| D5et x D5ot (e)      | c2:18 c5:180                | 4.86  | 70   | 85   | 134  | 237  | 524   |
| D5et x C10 (g)       | c2:18                       | 2.93  | 108  | 76   | 146  | 227  | 406   |
| D5et x C10t (f)      | c2:18 c5:36                 | 3.32  | 90   | 111  | 154  | 230  | 400   |
| C10 x C10t (h)       | c2:18                       | 2.93  | 0    | -    | -    | -    | 1236  (min 309) |
| C10t x C10t          | c1:36 c10:59292             | 14.53 | 0    | -    | -    | -    | 3348  |
| D5o x D5ot           | c2:18                       | 2.93  | 131  | 94   | 138  | 210  | 345   |
| D5o x D5et           | c2:18                       | 2.93  | 118  | 96   | 148  | 208  | 347   |
| D5o x C10t           | c2:18                       | 2.93  | 95   | 62   | 149  | 240  | 396   |
| C10 x D5ot           | c2:18                       | 2.93  | 111  | 76   | 152  | 224  | 363   |
| D5ot x D5ot          | c1:4 c2:16 c5:176           | 6.10  | 74   | 94   | 173  | 251  | 464   |
| D5ot x C10t          | c2:18 c5:36                 | 3.32  | 89   | 107  | 156  | 223  | 413   |
| D5ot x D5et          | (same as e)                 |       |      |      |      |      |       |
| untwisted pairs (D5e/D5o/C10 with each other) | - | - | - | - | - | - | disconnected by the residue argument |

Isomorphisms (checked by reasoning): conjugation by diag(2,1) in PGL(2,181) is an automorphism of G that maps
D5e -> D5o and fixes C10, so (D5e,D5ot) ~ (D5o,D5et), (D5e,C10t) ~ (D5o,C10t), (D5et,C10) ~ (D5ot,C10). Samples of
isomorphic pairs agree up to sampling noise (e.g. medUA 343 vs 345 for (a) vs D5o x D5ot). Also the family depends only
on the G-classes of L and R separately (X(G;L,R;D) = X(G;L,gRg^-1; D g^-1)), so the card's class list is enough.
Reference K (ref/K_scanA.tsv, 16,293 classes): median uBA+uAA = 368, 40 % have uBA+uAA <= 300.

## Exhaustive scan of pair (a) = D5e x D5et (card's pair with L = D5x0, R = D5')
Command (24 resumable chunks, each `timeout 100 nice -n 10 ../../cq/cq2 181 1 2 $D5e $D5et scanLR scan_D5e_D5et.tsv 300 k 24`,
k = 0..23, via chunk.sh; each chunk about 70 s for about 2470 members). Result: 59,292 members (= all regular double cosets
L z R; c10:59292 census), 59,292 unique ids, 22,860 connected (uBA+uAA <= 300, uBB computed; 38.6 %).
- Min C over connected members = 54, no C = 0 (no CLAIM). Histogram of the lowest values: 54 (8 members), 60 (8), 62 (8),
  64 (8), 68 (8), 70 (8), 72 (24), 74 (16), 76 (8), 80 (24), 82 (8), 84 (40). Median C over connected = 218.
- 10 best (id, z, uBA uAA uBB): 47939 (9 11 153 167 0) C 54; 47940 (same z, res 1) C 54; 50580 (9 73 90 167 0) C 54;
  50581 (same, res 1) C 54; 51953 (10 21 106 96 0) C 54; 51954 (res 1) C 54; 52113 (10 23 144 96 0) C 54;
  52114 (res 1) C 54; 28383 (3 38 86 64 0) C 60 (uBA 58 uAA 1 uBB 1); 28384 (res 1) C 60.
- Every member comes in a pair (z, z*(I,1)): the central Z2 twist flips the residue and gives the same costs.
- Best member re-checked with member mode: uBA 54 uAA 0 uBB 0 (C 54). Its 54 uncovered B-vertices are in
  regular (size-10) and size-2 orbits (unc mode, unc_best_47939.txt).
- Full-family medUA (uBA+uAA over all 59,292) = 366, so the sample estimate (343 / 362) was right.

Untwisted pairs (D5e x C10, C10 x C10, D5o x D5o, D5e x D5o, D5o x C10): all 297 members disconnected
(uBA+uAA about 593000), as the residue argument predicts.
