# haar_gen3: faster Haar search, more groups (notes)

Session 2026-10-23 (coordinator session_012VZAMpvqfDRmH7V6if1Sub, subagent). Files: `haar_gen3.c` (search),
`build_haar2.py` (independent checker for every family). `haar_gen.c`, `batch.sh`, `build_haar.py` and the watcher job
files are unchanged.

## Build and use

```
gcc -O3 -march=native -fopenmp -o haar_gen3 haar_gen3.c -lm
BIN=./haar_gen3 bash batch.sh JOBFILE           # same job lines as before: d D seconds seed K group... n
python3 build_haar2.py sols/<tag>.txt [/tmp/<tag>.edges.txt]   # prints ecc A/B, degrees, sha256, VALID/INVALID
```
CLI, RESULT line and solution file are the same as haar_gen's. For the old families (meta, sl/psl/pgl p prime, cyc)
the solution files are byte-compatible: `build_haar.py` still checks them, and `build_haar2.py` writes the identical
edge list (same element order), so the sha256 agrees with `build_haar.py`'s edge file (checked on
d7D8_psl_17_17_s1: both 82594e26…).

Wave-3 recipe and job lists for the watchers: `wave3/WAVE3.md`.

## 1. Speed

### Where the time went (haar_gen)
Each candidate evaluation = rebuild two N-entry left-multiplication tables (N matrix products with a p^4 lookup) +
one or two BFS over the full Haar graph with N-sized uint32 mark arrays: N·d random accesses per BFS level, out of
cache for N ≳ 10^5. 2.7 ms/eval at N = 41,616 (d7D8), 130 ms/eval at N = 565,440 (d8D9).

### What haar_gen3 does
- **Bitset BFS over cosets of a cyclic subgroup.** Pick H = ⟨h⟩ ≤ G cyclic of the largest order nH ≤ 63 (found by
  sampling element orders). Element g = rep_r·h^b is bit b of row r (left cosets gH). Left multiplication by s maps
  row r to one row r' with a rotation: s·rep_r = rep_r'·h^j ⇒ s·rep_r·h^b = rep_r'·h^(j+b). So one BFS level is
  (rows)·d word operations (OR of a rotated 64-bit word) instead of N·d random accesses, and every table is N/nH long
  (L2 resident). Works for any group (H need not be central or normal), not only M × Z_n.
- The table of s⁻¹ is the inverse permutation of the table of s (no extra multiplications); a candidate costs N/nH
  group products.
- Sparse frontier lists for the first BFS levels, dense row sweeps once the frontier is > R/16 rows.
- Matrix groups indexed by a q³-size key (not p⁴), so q up to ~200 fits easily.
- `THREADS=t`: the K candidates of a move are evaluated in parallel (OpenMP). On this container, with the other
  cores busy, 2 threads gave no more evaluations per second than 1 (17.7k vs 18.4k in 20 s with
  `OMP_WAIT_POLICY=passive`; without it the spinning threads halved throughput). Not measured on idle cores; four
  independent seeds (four batch.sh queues) are the better use of a 4-core box anyway, since near a wall solve times
  are heavy-tailed.
- An accepted candidate's coverage bitsets are kept, so building the targeted-move lists needs no extra BFS.

### Benchmarks (this container, Xeon 2.1 GHz, 1 thread per run)

Per evaluation:

| case | N | haar_gen | haar_gen3 | speedup |
|---|---|---|---|---|
| d7D8 psl 17 × Z17 | 41,616 | 2.72 ms | 0.040 ms | 68× |
| d8D9 psl 31 × Z38 | 565,440 | 130 ms | 0.87 ms | 150× |
| d7D10 psl 29 × Z82 (2 tables + 1 BFS) | 998,760 | ~190 ms | 0.88 ms | ~200× |
| d8D10 pgl 31 × Z117 | 3,481,920 | – | 5.4 ms | |
| d13D8 SL(2,9) × SL(2,13) × Z2 | 3,144,960 | – | 6.9 ms | |

Time to solution, same jobs (K = 8, seconds):

| job | haar_gen | haar_gen3 |
|---|---|---|
| `7 8 … psl 17 17`, seeds 1–6 | 40.6, 16.6, 8.0, 90.3, 90.5, 169.1 (mean 69) | 2.2, 1.7, 0.6, 1.3, 0.5, 1.0 (mean 1.2); seeds 7–12: 2.3, 5.7, 1.4, 11.7, 3.8, 1.1 |
| `8 9 … psl 31 38`, seeds 1–3 (600 s cap) | 4.9, fail (best 2), fail (best 4) | 10.9, 91.1, 38.3; seeds 7–12: 34.6, 40.6, 70.5, 1.6, 12.0, 7.2 (12/12 solved) |

## 2. Group families (haar_gen3 and build_haar2.py)

`GROUP` grammar (then the cyclic factor n, as before):
- `meta m k r`, `cyc` — as before.
- `sl q`, `psl q`, `pgl q` — **q any prime power** (GF(p^k) = GF(p)[x]/(f), f the smallest monic irreducible; the
  spec in the solution file then reads e.g. `psl 27 poly x^3+2x+1`, field elements written as Σ c_i p^i).
  New orders: PSL(2,q) for q = 8, 9, 16, 25, 27, 32, 49, 64, 81, 121, 125, 128, 169, 243, 256 … (PSL(2,49) = 58,800,
  PSL(2,64) = 262,080, PSL(2,81) = 265,680, PSL(2,121) = 885,720, PSL(2,125) = 976,500, PSL(2,128) = 2,097,024).
- `agl1 q` — affine group x ↦ ax + b over GF(q), order q(q−1).
- `prod G1 G2` — direct products, nestable, e.g. `prod psl 7 psl 11` (110,880), `prod psl 5 psl 9` (21,600 = A5 × A6).
- `tpgl q` — twisted Z_n ⋊ PGL(2,q): (m,z)(m',z') = (mm', z + χ(m)z'), χ = quadratic character of det. Only as the
  whole group. **Bad** (see below): every involution of PGL∖PSL gives n involutions.
- `csl q` — central product (SL(2,q) × Z_n)/⟨(−I, n/2)⟩, n even. For n ≡ 2 mod 4 it is ≅ SL(2,q) × Z_{n/2}; for
  4 | n it has many involutions. Kept for completeness; no advantage seen.

Checker: `build_haar2.py` rebuilds every family from its definition (brute-force matrix enumeration over GF(q) with
the field built from the polynomial in the spec and checked irreducible), and was run on a solution of every new
family (psl 27, pgl 16, agl1 49, prod psl 4 psl 7, sl 9, psl 8, psl 25, prod meta psl 9, psl 9, agl1 32): all VALID.

## 3. What makes a group good (observations, this session)

Short cycles: if s_i⁻¹s_j has order k, every vertex lies on a 2k-cycle, which wastes words of length ≥ k. So the
density f_k of elements of order k (k = 2..6) should matter. `wave3/group_score.py` computes f_k exactly for
SL/PSL/PGL(2,q) × Z_n and products (class formulas) and a score Σ f_k/(d−1)^(k−2); `make_jobs3.py --best F` keeps
the best-scoring fraction. Evidence at equal order (1 thread, same K):

| cell, N | group | f2 | result |
|---|---|---|---|
| (6,9), 58,752 | SL(2,17) × Z12 | 5e-5 | solved 0.4 s (seed 101); best 2 in 60 s (seeds 1, 2) |
| | PSL(2,17) × Z24 | 5e-3 | best 6 (180 s) |
| | PGL(2,17) × Z12 | 1e-2 | best 7 (180 s) |
| | csl 17 × Z24 | | best 5, 5 (60 s) |
| | PSL(2,49) | 2e-2 | best 23 (180 s) |
| | tpgl 17 × Z12 | 3e-2 | best 42, 37 (60 s) |

So simple groups alone (n = 1) and groups rich in involutions are bad; SL(2,q) (one involution) is good. But the
score is not everything: A5 × A6 × Z5 (f2 = 7e-3) solved (8,8) at 108,000 in 48 s.

**Random-S screening beats the score.** `RANDSAMPLE=m haar_gen3 d D 1 1 8 /dev/null GROUP n` prints quantiles of the
cost of m random generator sets (no search; ~0.1–1 s per group at m = 300–1000). On (6,9) at 58,752 the p10 order
(SL 42 < PSL 54 = csl 54 < PGL 68 < PSL(2,49) 83 < tpgl 151) is exactly the annealing order. `make_jobs3.py
--screen m` ranks candidates by (p10 + median) / (N e^(−W/N)) (normalised so different orders compare) and
`wave3/pick_top.py K` keeps the best K. The screen found the winners below: SL(2,7) × SL(2,9) for (6,10) and (9,8)
(top-ranked at its order), SL(2,q) × small Z_n with large q for (7,10) and (8,9).

**Products of two SL(2,q)** (no cyclic factor, perfect group, few small-order elements) are very strong:
SL(2,7) × SL(2,9) = 241,920 solved (6,10) in 2.3 s and (9,8) in 9.8 s; SL(2,5) × SL(2,17) = 587,520 solved (8,9)
in 1 s (761 evaluations).

**Search knobs** (restart from random, faster reheat, secondary slack objective): no measurable gain on
`6 9 … sl 17 12` (4 seeds × 45 s each: default 1/4 solved, RESTART=1 REHEAT=5 0/4, REHEAT=5 1/4). Near a wall
the search sits on a cost-1 or cost-2 plateau; what helps is more groups and more seeds, not tuning.

## 4. Results of this session (haar_gen3, this container, ≤ 3 cores, ~2.5 h of runs)

All rebuilt with `build_haar2.py` (two BFS from (e,A) and (e,B): ecc ≤ D, unreached 0, max = min degree = Δ, no
repeated edge). sha256 = of the edge list `n` + `u v` lines as written by build_haar2.py (= build_haar.py's format and
order for the old families). Files: `sols/<tag>.txt`, `runs/<tag>.log`, `runs/<tag>.rebuild.txt`.

| cell | group | N | vertices | previous best (vertices) | tag | edge-list sha256 |
|---|---|---|---|---|---|---|
| (6,9) | sl 17 x Z_12 | 58,752 | 117,504 | none; table 117,360 (new cell) | d6D9_sl_17_12_s101 | 3cefda3aac28d9112fd1037f6b4b00b9f16e30182a056a79adaaa7a36e0f3e62 |
| (6,10) | psl 27 poly x^3+2x+1 x Z_25 | 245,700 | 491,400 | 482,160 | d6D10_psl_27_25_s101 | b1b77f30fab083a640952abbe386862fcc099c04f63f40310812aff41834a218 |
| (7,9) | sl 31 x Z_7 | 208,320 | 416,640 | 410,640 | d7D9_sl_31_7_s111 | 3d3b74e4b749094f544807e0397dcee2da3576a9f8a0494fcef337cbbee05409 |
| (7,10) | sl 49 poly x^2+1 x Z_9 | 1,058,400 | 2,116,800 | 2,075,520 | d7D10_sl_49_9_s101 | 73ef408e888516f5ad9b3bee1333cb298f954286e275d2c4c237256273ddb0e8 |
| (8,8) | psl 29 x Z_9 | 109,620 | 219,240 | 210,528 | d8D8_psl_29_9_s101 | 0c4ba39a4bb612d9af61dcb0ccd793eab042c154a841f01d9e30d0a25ff9b211 |
| (8,9) | sl 59 x Z_3 | 615,960 | 1,231,920 | 1,169,280 | d8D9_sl_59_3_s101 | f41383998754bba80b1372e46337733adf33b196466720ae74ee5d8198e0be01 |
| (8,10) | sl 107 x Z_3 | 3,674,808 | 7,349,616 | 7,143,552 | d8D10_sl_107_3_s111 | ecde263dc881283548aa7d5d1e4c47ecba1ff0840c78d115a94c39c21b19fb5e |
| (9,8) | prod sl 7 sl 9 poly x^2+1 x Z_1 | 241,920 | 483,840 | 476,784 | d9D8_prod_sl_7_sl_9_1_s101 | 610caefd2f73800f43fd9174b245c7f5a6298ab9cd4c7b33057a6e54693530d5 |
| (9,9) | sl 81 poly x^4+x+2 x Z_3 | 1,594,080 | 3,188,160 | 2,976,480 | d9D9_sl_81_3_s111 | 344a85abc21b165c94367543d2e0bf62ccf64284efb023ca61d94926c0e9a602 |
| (9,10) | sl 223 x Z_1 | 11,089,344 | 22,178,688 | none; table 20,017,260 (new cell) | d9D10_sl_223_1_s111 | d29df0b77b1bf5436dff17a10b0d68d717d0d55a586a145313de79c527d977cb |
| (10,9) | prod psl 5 sl 25 poly x^2+2 x Z_4 | 3,744,000 | 7,488,000 | 7,349,616 | d10D9_prod_psl_5_sl_25_4_s111 | d91dddbfa77ffe35e38bdeb20baa461d4904de3d80844c1b002c00c5da5cf251 |
| (11,9) | prod sl 7 sl 29 x Z_1 | 8,184,960 | 16,369,920 | none; table 15,200,448 (new cell) | d11D9_prod_sl_7_sl_29_1_s111 | f0685bc56672428602cdc50cddad9abf2f10a064dd4936cc03f9d8b0cf2d2d43 |
| (13,8) | prod sl 7 sl 11 x Z_7 | 3,104,640 | 6,209,280 | 5,725,440 | d13D8_prod_sl_7_sl_11_7_s101 | c1390148325ab758d9bf9241bf526bc46d8a674049ab586431f36d4f15269046 |

Walls seen (orders tried above the best, all with cost 1–4 left after 150–600 s):
- (8,8): best 109,620; unsolved at 109,440 (SL(2,19)×Z16, best 1), 110,880 (A5×PSL(2,7)×Z11, 2), 112,896 (2),
  109,200 PGL(2,13)×Z50 (1), 106,080 PSL(2,16)×Z26 (1).
- (7,8): best stays 44,064 (watchers): 44,310 AGL(1,211) (1), 44,460 PSL(2,19)×Z13 (1, two seeds), 44,640 PSL(2,31)×Z3
  (2), 44,880 PSL(2,16)×Z11 (3), SL(2,11)×Z34 (4), PGL(2,9)×Z62 (5).
- (6,10): best 245,700; 252,960 PSL(2,31)×Z17 (2), 253,080 SL(2,37)×Z5 (1).
- (9,8): best 241,920; 244,800 SL(2,5)²×Z17 (1), 262,080 SL(2,5)×SL(2,13) (4).
- (7,9): best 208,320; 207,060 PSL(2,29)×Z17 (2), 216,000 products (5, 6), 216,216 SL(2,27)×Z11 (6).
- (7,10): best 1,058,400; 1,062,720 SL(2,81)×Z2 (1, two seeds), 1,062,936 SL(2,37)×Z21 (1), 1,073,520 SL(2,71)×Z3 (2).
- (8,9): best 615,960; 619,920 SL(2,41)×Z9 (2), 620,928 (2), 622,656 SL(2,47)×Z6 (2), 633,600 (6), 655,200 (12).
- (9,9): best 1,594,080; 1,637,064 SL(2,53)×Z11 (4), 1,642,560 SL(2,59)×Z8 (6 at 240 s).
- (8,10): best 3,674,808; 3,694,968 PSL(2,73)×Z19 (1), 3,719,520 SL(2,81)×Z7 (1).
- (10,9): best 3,744,000; 3,769,920 PSL(2,11)×SL(2,7)×Z17 (2), 3,801,600 PSL(2,9)×SL(2,11)×Z8 (2).
- (9,10): best 11,089,344; 11,232,000 SL(2,9)×SL(2,25) (2).
- (11,9): best 8,184,960; 8,265,600 SL(2,5)×SL(2,41) (2).
- (13,8): best 3,104,640; 3,111,552 SL(2,73)×Z8 (1), 3,144,960 PSL(2,13)×SL(2,9)×Z4 (1), 3,231,360 (4).
In N_h units (heuristic.py) the walls sit at 0.80–0.86: (7,8) 0.86, (6,9) 0.84, (8,8) 0.83, (6,10) 0.83,
(7,10) 0.83, (7,9) 0.82, (8,9) 0.81, (9,9) 0.80, (9,8) 0.80, (13,8) 0.79.

New cells (no earlier Haar graph of ours): (6,9), (9,10), (11,9). The two huge new cells were nearly free: at
0.75·N_h random generator sets already have cost 0 (RANDSAMPLE min = 0), so the search only polishes. Cells with
table/N_h around 0.75 or less that nobody here has tried yet: (12,9) (table 30,001,152 → N 15.0M, 0.73),
(13,9) (50,990,610 → N 25.5M, 0.66), (10,10) (50,331,156 → N 25.2M, 0.71), (14,9), (15,9), (16,9). These need
N = 15–145M; haar_gen3's memory is ~10 bytes per element plus O(N/60) tables, so 25M is fine on this box,
and build_haar2.py checked 22M vertices in 270 s.
