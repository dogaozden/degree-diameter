# hcheckpsl: diameter checker for Haar graphs H(PSL(2,p) x Z_n, S)

Independent multithreaded C checker, written from the card's definitions (no other checker's source was read or copied).
Source: `hcheckpsl.c`. Binary: `hcheckpsl`.

## Build and usage

    gcc -O3 -fopenmp -Wall -o hcheckpsl hcheckpsl.c

    THREADS=2 nice -n 10 ./hcheckpsl FILE     # prints VALID or INVALID, then the ecc line; exit 0 iff VALID (1 = INVALID, 2 = usage/IO error)
    ./hcheckpsl --selftest                    # index, Barrett and BFS self-tests; exit 0 iff all pass
    VERBOSE=1 THREADS=2 ./hcheckpsl FILE      # also prints per-step BFS timing on stderr (does not change the computation)

Output format:

    VALID d=10 D=10 group=psl 389 x Z_1 N=29431740 vertices=58863480
    ecc(e,A)=10 ecc(e,B)=10

## Method (short)

* Group element (M,z): M in PSL(2,p), z in Z_n. Canonical M (sign fixed): a in [1,(p-1)/2], or a = 0 and c in [1,(p-1)/2].
  Index of M: `(a-1)p^2 + cp + b` if a != 0, `H p^2 + (c-1)p + d` if a = 0 (H = (p-1)/2). Bijective onto [0,P), P = p(p^2-1)/2;
  element index = psl_index*n + z. Inverse map by arithmetic (d or b from ad-bc = 1). Verified exhaustively for p <= 23 and by random sampling for p = 151, 389, 1009.
* Vertices (g,A), (g,B); edges (g,A) ~ (s g,B) with s g = (M_s M, z_s+z); (h,B) ~ (s^-1 h,A) with s^-1 = (adj M_s, -z_s).
  Right multiplication is an automorphism, so diameter = max(ecc(e,A), ecc(e,B)).
* Storage: one 2-bit field per vertex (0 = unseen, 1+(level mod 3) otherwise), 4 bits per group element. The 2n fields of one PSL
  element are contiguous, so each (PSL element, generator) product is computed once and its target block is written in one pass.
* BFS: push from the frontier of the parity-matching side; the frontier is every field equal to 1+(t mod 3). Older vertices with
  the same label (levels t-6, ...) are also scanned, but their neighbours are already labelled, so they set nothing. New labels:
  plain test, then atomic OR, so a label is never overwritten. Eccentricity is the exact value (BFS runs until the frontier empties).
* z given outside [0,n) or entries outside [0,p) are reduced mod n / mod p. Checks: header literal tokens, header N = n p(p^2-1)/2,
  p odd prime, det = 1 mod p for every matrix, generators distinct as PSL x Z_n elements, exactly d generator lines.

## Self-tests (`./hcheckpsl --selftest`, THREADS=2): all pass

* Barrett reduction vs `%`: 5 moduli x 10^6 random 64-bit inputs plus edge values: ok.
* Index bijection, exhaustive p = 3,5,7,11,13,17,19,23: every index hit by exactly the two matrices +-M; decode/encode round trip; ok.
* Index random draws p = 151, 389, 1009 (200000 draws each): ok.
* BFS against a naive reference (explicit sorted list of PSL matrices, plain queue BFS): 400/400 random instances agree on
  eccentricities and reached counts, largest eccentricity seen 55 (exercises the mod-3 labels well past the wrap).

## Test results

Test 1, valid solutions (expected VALID). Both checkers run with THREADS=2, `nice -n 10`, `timeout 600`, 2 GB address-space cap.

| file | ours | hcpsl (reference) | ours ecc(e,A),ecc(e,B) | ours wall (s) | hcpsl wall (s) |
|---|---|---|---|---|---|
| d6D10_psl_23_38_s1 | VALID | VALID | 10, 10 | 0.07 | 0.29 |
| d6D10_psl_29_19_s1 | VALID | VALID | 10, 10 | 0.20 | 0.30 |
| d7D10_psl_29_82_s2 | VALID | VALID | 10, 10 | 0.30 | 0.79 |
| d11D8_psl_59_11_orb5_ORBW5_s3 | VALID | VALID | 8, 8 | 0.33 | 1.16 |
| d13D8_psl_79_13_s404 | VALID | VALID | 8, 8 | 0.60 | 3.49 |
| d15D8_psl_137_7_orb3f0_s1 | VALID | VALID | 8, 8 | 2.15 | 10.73 |
| d10D10_psl_389_1_orb3_s1 | VALID | VALID | 10, 10 | 13.20 | 28.32 |

Test 2, corrupted copies (expected INVALID). Copies are in `corrupt/`, made by `make_corrupt.py`:
(a) z of generator 2 changed by +1 mod n; (b) header D lowered by 1; (c) generator 2 replaced by a random det-1 matrix (fixed seed), z kept.
Case (a) is not applicable to d10D10_psl_389_1 (n = 1: z is always 0, so the change is a no-op).

| base file | (a) z+1: ours / hcpsl (ecc) | (b) D-1: ours / hcpsl (ecc) | (c) random matrix: ours / hcpsl (ecc) |
|---|---|---|---|
| d6D10_psl_23_38_s1 | INVALID / INVALID (11,11) | INVALID / INVALID (10,10) | INVALID / INVALID (11,11) |
| d6D10_psl_29_19_s1 | INVALID / INVALID (11,11) | INVALID / INVALID (10,10) | INVALID / INVALID (11,11) |
| d7D10_psl_29_82_s2 | INVALID / INVALID (11,11) | INVALID / INVALID (10,10) | INVALID / INVALID (11,11) |
| d11D8_psl_59_11_orb5_ORBW5_s3 | INVALID / INVALID (9,9) | INVALID / INVALID (8,8) | INVALID / INVALID (9,9) |
| d13D8_psl_79_13_s404 | INVALID / INVALID (9,9) | INVALID / INVALID (8,8) | INVALID / INVALID (9,9) |
| d15D8_psl_137_7_orb3f0_s1 | INVALID / INVALID (9,9) | INVALID / INVALID (8,8) | INVALID / INVALID (9,9) |
| d10D10_psl_389_1_orb3_s1 | n/a (n = 1) | INVALID / INVALID (10,10) | INVALID / INVALID (11,11) |

The ecc values in this table are ours (exact eccentricities). hcpsl prints the reach within D, not the exact eccentricity, for
INVALID inputs; in all 20 cases it fails to reach every vertex within D, consistent with our ecc > D.

Test 3, agreement of verdicts: 27/27 files agree (7 valid + 20 corrupted). On the 7 valid files our eccentricities equal hcpsl's exactly.

Test 4, timing (THREADS=2):

* d10D10_psl_389_1_orb3_s1 (N = 29,431,740, n = 1): ours 13.2 s wall (BFS from (e,A) 6.68 s, from (e,B) 6.51 s, max RSS 18 MB);
  hcpsl 28.3 s. Caveat: n = 1 is the worst case for this block layout (each block carries one z value, so each (block, generator)
  product is paid per vertex).

PENDING_SYNTH

## Files

* `hcheckpsl.c`, `hcheckpsl` (binary).
* `make_corrupt.py` -> `corrupt/` (20 copies). `run_tests.sh LIST OUT.tsv` runs both checkers one process at a time.
* `results/` (test TSVs and file lists), `logs/` (stdout/stderr of every run, both checkers).
* `synthetic/gen_synth.py` and `synthetic/synth_psl_151_1321_d16.txt`: random timing-only instance (same p, n, d, N as the
  d16D10_psl_151_1321 target; those files were not opened).
