# h02 table: Z_m x_r Z_k, (4,11), plain random S (haar_gen3, THREADS=1, nice 10)
Command pattern: THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 4 11 <secs> <seed> 4 OUT meta m k r 1   (run.sh)
"best" = min uncovered at end (0 = solved). Each row: group, N, k, p, Frobenius?, centre, H order (bitset path), runs.

| group | N | k | Frob. | H order | run (seed, secs) | result | evals | note |
|---|---|---|---|---|---|---|---|---|
| Z_163 x_r Z_81 (r=4) | 13203 | 81 | yes | 27 | s1, 90 | SOLVED, 2.4 s | 3,533 | scorer VALID + apsp VALID, 26,406 vertices |
| Z_313 x_r Z_39 (r=256) | 12207 | 39 | yes | 39 | s1, 90 | SOLVED, 0.0 s | 17 | haar_gen3 internal check only |
| Z_271 x_r Z_45 (r=44) | 12195 | 45 | yes | 45 | s1, 90 | SOLVED, 0.0 s | 9 | haar_gen3 internal check only |
| Z_421 x_r Z_35 (r=307) | 14735 | 35 | yes | 35 | s2, 90 | **SOLVED, 37.8 s** | 73,441 | scorer VALID + apsp VALID, **29,470 vertices** |
| Z_421 x_r Z_35 (r=307) | 14735 | 35 | yes | 35 | s1, 90 | cost 2 | 176,877 | not solved |
| Z_421 x_r Z_35 (r=307) | 14735 | 35 | yes | 35 | s3, 90 | cost 2 | 193,509 | not solved |
| Z_421 x_r Z_35 (r=307) | 14735 | 35 | yes | 35 | s5, 90 | cost 2 | 172,137 | not solved |
| Z_421 x_r Z_35 (r=27, r1 g02) | 14735 | 35 | yes | 35 | s1, 25 | cost 2 | 51,313 | from round 1 |
| Z_469 x_r Z_33 (r=4, m=7*67, ord 3 and 33) | 15477 | 33 | NO (trivial centre) | 33 | s1, 90 | cost 8 | 149,229 | composite relaxed, not Frobenius |
| Z_463 x_r Z_33 (r=179) | 15279 | 33 | yes | 33 | s1, 90 | cost 4 | 134,713 | |
| Z_463 x_r Z_33 (r=179) | 15279 | 33 | yes | 33 | s2, 90 | cost 6 | 166,069 | |
| Z_463 x_r Z_33 (r=179) | 15279 | 33 | yes | 33 | s3, 90 | cost 4 | 167,741 | |
| Z_463 x_r Z_33 (r=179) | 15279 | 33 | yes | 33 | s4, 90 | cost 4 | 150,901 | |
| Z_307 x_r Z_51 (r=275) | 15657 | 51 | yes | 51 | s1, 90 | cost 10 | 213,637 | |
| Z_307 x_r Z_51 (r=275) | 15657 | 51 | yes | 51 | s2, 90 | cost 8 | 246,637 | |
| Z_167 x_r Z_83 (r=25) | 13861 | 83 | yes | 1 (slow path) | s1, 90 | cost 4 | 8,317 | prime k > 63: no cyclic H, ~90 evals/s |
| Z_179 x_r Z_89 (r=4) | 15931 | 89 | yes | 1 (slow path) | s1, 90 | cost 22 | 6,633 | prime k > 63: underpowered |

Frobenius groups Z_p x_r Z_k (k odd, r of order k) with N in 14,460-16,500 (only these exist): (k,p) = (33,463), (35,421),
(51,307), (89,179). Squarefree composite m = p1 p2 with k | gcd(p1-1,p2-1) needs p_i = 1 mod 2k, so N >= k(2k+1)^2:
none exists for k >= 33 in range (smallest is ~440k vertices). Non-Frobenius composite Z_469 x_r Z_33 has trivial centre.

Summary: Z_421 x_r Z_35 solved 1 of 4 seeds at 90 s (seed 2 at 38 s); Z_463 x_r Z_33 best cost 4 in 4 seeds; Z_307 x_r Z_51 best 8-10.
