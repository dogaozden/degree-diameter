# raise-d12: D = 12 Haar graphs with field-automorphism orbits (job raise-d12, 2026-11-01/02)

Branch claude/d12-frontier-cells-m24ikx. Results and the write-up: research/frontier/beyond/BEYOND_TABLE.md (section
"D = 12: field-automorphism orbits ..."); squad rounds: research/squads/raise-d12/, research/squads/LOG.md.

## Files

- `haar_bigq.c`: haar_big0 (research/frontier/beyond11/haar_big0.c) for G = SL(2,q) x Z_n or PSL(2,q) x Z_n with
  q = p^e any prime power <= 4096. Field: GF(p)[x]/(f), f the first monic irreducible in haar_sym's order, elements as
  integers sum c_i p^i (the convention of haar_sym and haarcheck_gen). Rows of the bit-parallel BFS are left cosets of
  the split torus T = {diag(l, 1/l)} (mod +-1 for PSL) times Z_n, which is cyclic of order |T| n when gcd(|T|, n) = 1
  (|T| = q - 1 for SL, (q - 1)/2 for PSL); left multiplication by a generator permutes rows and rotates each row, as in
  haar_big0. AFROB=j makes alpha the field automorphism x -> x^(p^j) (order e/gcd(e,j)) times z -> r z; FIXORD=o picks
  the alpha-fixed generators among elements of order o. All other options (ORBIT, RANDORB, START, EVAL, UNCPRINT,
  THREADS, ...) are haar_big0's. Build: `gcc -O3 -march=native -fopenmp -o haar_bigq haar_bigq.c -lm`.
  Validation: EVAL gives cost 0 on four known-valid solution files (psl 81 x Z121 at D = 10, sl 81 x Z7 at D = 9,
  sl 64 x Z13 at D = 8, psl 167 x Z61 at D = 12), and on corrupted copies (one generator transposed) the same cost as
  haar_big0 (19, prime field) and as haarcheck_gen's unreached count (53, GF(81)); probe/bad_*.txt.
- `check.sh SOL [threads]`: runs research/frontier/haarcheck_gen.c (independent code: own field and group arithmetic,
  BFS from (e,A) and from (e,B)) and writes research/frontier/runs/cloudcheck/<stem>.gen.txt.
- `randloop.sh`: RANDORB batches until a cost-0 sample is written. `after_check.sh`: starts the (11,12) search when the
  (15,12) check has freed its memory. `cellstats.py d D 2N`: Moore bound, % of M_b, size-law mu, size-law 2N at mu = 5.
- `runs/`: search logs and outputs (the solution files are copied to research/frontier/sols/).

## Commands of the finds

```
ORBIT="7 1 1" AFROB=1 RANDORB=420 THREADS=1 haar_bigq 8 12 100 2 4 OUT sl 128 71          # (8,12), 3 of 420 samples
ORBIT="7 1 2" FIXORD=3 AFROB=1 THREADS=2 haar_bigq 9 12 3000 21 6 OUT sl 128 281          # (9,12), 1,444 evaluations
ORBIT="5 2 0" AFROB=1 THREADS=2 haar_bigq 10 12 2400 11 4 OUT psl 243 271                 # (10,12), 626 evaluations
ORBIT="3 5 0" THREADS=4 haar_big0 15 12 900 1 4 OUT psl 197 3924                         # (15,12), first S
```
