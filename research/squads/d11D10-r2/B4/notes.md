# B4: checker readiness for psl 243 (draft, updated at the end of the run)

Started 12:49 UTC, time box 40 min. Budget 6 slot-min. Every heavy command went through gate.sh (THREADS unset, `env -u THREADS`).

## Files in this folder
- `d16D8_psl_243_1_orb5_frob1_s1.txt`: valid #1, haar_sym `ORBIT="5 3 1" AFROB=1 haar_sym 16 8 60 1 8 <file> psl 243 1`
  (Delta 16, D 8, G = PSL(2,243), n = 1, 2|G| = 14,348,664 vertices). haar_sym: cost 0 at the start (evals 1),
  "full diameter check: OK", "wrote". |Fix(alpha)| = 11 (+e), mu = 0.00.
- `d16D8_psl_243_1_plain_s2.txt`: valid #2, same without ORBIT (`haar_sym 16 8 60 2 8 <file> psl 243 1`). [see status below]
- `corrupt_repeat_from_s1.txt`: valid #1 with generator 7 replaced by a copy of generator 3 (repeated generator).
- `corrupt_breakdet_from_s2.txt`: valid #2 with one entry of generator 5 changed, det != 1.
- `big_psl_243_11_r11_s1.txt`: 157,835,304-vertex test file, psl 243 x Z_11, D = 10, N = 78,917,652, 11 random generators
  (seed 1, s_0 = e). INVALID by construction; only used for timing and memory.
- `mkcases.py` (file builder, GF(243) = GF(3)[x]/(x^5+2x+1)), `runtimed.py` (wall time, peak RSS, timestamped output),
  `chain_small.sh` (sequential checks inside one gate slot), `logs/`.

## Checker facts (read from the sources in research/squads/d11D10-r1/{B2/haarcheck_pq.c, opus/pqcheck.c})
- haarcheck_pq: BFS from (e,A) and (e,B) by levels to the full eccentricity (no early exit). Eccentricity = number of
  productive levels (exact). Memory about 4|G| bits.
- pqcheck: BFS stops at D+2 levels. Its ecc counts the final empty level when the graph is not fully reached, so
  eccentricities of disconnected graphs are one too large (verdicts unaffected). Progress lines on stderr per level.
  Keeps SL->PSL table (4|SL| bytes) and 6 bitsets.
- haar_sym has no check-only mode (CKPT resume only accepts alpha-invariant S), so haar_sym's own verdict is available only
  for the files it writes. For the corrupted copies the reference is the definition (simple graph / SL(2,243) matrices).

## Results
(pending: filled in below when the runs finish)
