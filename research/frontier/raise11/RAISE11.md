# raise-d11: raising the D = 11 values (job of 2026-11-01/02)

Opus director with Haiku squad rounds (research/squads/raise11/, log in research/squads/LOG.md), branch
claude/raise-d11-frontier-26r11l. This note is the director's summary; the table rows are in
research/frontier/beyond/BEYOND_TABLE.md.

## What changed the picture

The beyond-d11 and beyond-d11b jobs stalled at size-law mu ~ 7-11 at D = 11 and concluded that odd D was hard. Round 1
of this job found that the wall was mostly **group choice**: SL(2,p) x Z_n (or PSL) with **small n** and the standard
orbit shape solves at mu ~ 15 within a few fresh runs.

- Card r1/c13 wrote a clump model (research/squads/raise11/r1/c13/MODEL.md, model.py): with S closed under alpha
  (order 3) the holes come in clumps (alpha x inversion: 6 generic elements; alpha-fixed torus elements, ~p of them,
  missed with prob ~exp(-lambda/3) and paired by inversion; central elements (+-I, z), 2n of them, missed with prob
  ~exp(-lambda/5); -I and the PSL involutions). K = the expected number of independent clumps over both sides, and
  P(cost 0 for a fresh run) ~ exp(-K). It ranks SL(2,p) x Z_n with n = 1..31 and p a few hundred above the large-n and
  PSL groups the earlier jobs used. rank11.py lists groups above a value ranked by K.
- Card r1/c06 tested the model's first pick at (8,11): SL(2,149) x Z7, mu 15.3, solved in 25 s (+2.16 %). The director
  then solved (12,11) SL(2,601) x Z7 (mu 10.65, +2.12 %) in 5 evaluations; the beyond-d11 job had stopped this group
  after 48 evaluations at cost 6.
- Card r1/c09 measured the hole anatomy: at n >= 229 about a quarter of the holes are central elements.
- Fresh seeds beat resumed chains (cards c07, c08, c16): near the limit the annealer's cost 2-6 states are local minima.
- The model over-penalises moderate n with PSL: (7,11) PSL(2,47) x Z109 (model K 17) solved at mu 15.2 (card c04).

## Results (all independently checked; table rows in research/frontier/beyond/BEYOND_TABLE.md)

| cell | was | now | gain | group | found by | checks |
|---|---:|---:|---:|---|---|---|
| (5,11) | 311,426 | 312,206 | +0.25 % | Frobenius Z4219 x\|_2565 Z37, plain random S | squad r5/h02 (haar_meta) | metacheck, build_haar2.py |
| (6,11) | 2,122,518 | 2,137,526 | +0.71 % | Frobenius Z15053 x\|_5955 Z71, plain random S | squad r4/g05 (haar_meta) | metacheck, build_haar2.py |
| (7,11) | 11,012,976 | 11,426,448 | +3.75 % | SL(2,67) x Z19, ORBIT "3 2 1" | squad r3/f01 | haarcheck_gen, haarcheck_lean |
| (8,11) | 45,329,808 | 46,547,568 | +2.69 % | SL(2,107) x Z19, ORBIT "3 2 2" | squad r4/g02 | haarcheck_gen, haarcheck_lean |
| (9,11) | 155,250,816 | 159,415,392 | +2.68 % | SL(2,137) x Z31, ORBIT "3 3 0" | director loop (600-s run) | haarcheck_gen, haarcheck_lean |
| (10,11) | 460,691,568 | 469,768,992 | +1.97 % | SL(2,617), ORBIT "3 3 1" | director loop | haarcheck_gen |
| (12,11) | 2,976,066,240 | 3,039,136,800 | +2.12 % | SL(2,601) x Z7, ORBIT "3 4 0" | director (5 evaluations) | haarcheck_gen (3,781 s) |
| (16,11) | 29,961,590,400 | 33,763,363,200 | +12.69 % | PSL(2,449) x Z373, ORBIT "3 5 1", first random S | director | haarcheck_gen (see the run log) |

Intermediate values also found and checked: (5,11) 311,942 (Z8209 x| Z19); (6,11) 2,124,866 (Z25913 x| Z41) and
2,135,280 (PSL(2,41) x Z31, orbit search); (7,11) 11,311,584 (PSL(2,47) x Z109); (8,11) 46,309,200 (SL(2,149) x Z7) and
45,445,680 (PSL(2,71) x Z127, card check only); (10,11) 461,335,200 (SL(2,151) x Z67).

Not raised: (11,11) (SL(2,449) x Z7 at +2.09 % reached cost 6-8 in 600-s runs of ~70 evaluations; the (9,11) solve needed
851), (13,11), (14,11), (15,11) (searches stopped to keep the machine free for checks), (3,11), (4,11).

## Lesson on run length

At Δ >= 9 a lineage needs ~10^3 evaluations before it reaches cost 0 (the (9,11) solve came at evaluation 851 of a 600-s
run). Under load a 95-s card run gets 70-100 evaluations there, so cards stalled at cost 2 on the very group that the
director then solved on the first 600-s run. "Fresh seeds beat resumes" is still true, but each fresh seed needs a full
run. For card rounds: give Δ >= 9 to longer director loops, or let cards chain resumes of the same lineage.

## Negative results

- Inverse-closed S (S = S^-1, so the Haar graph is the bipartite double of a Cayley graph and only one side needs
  covering; haar_sd.c SYM=1): with e in S the words collapse (u e u^-1 = e: 10^5-10^6 holes); without e the per-side
  holes double, which cancels the gain; card c12 found it 8-10x worse at SL(2,41) x Z331 (central elements gain
  one-letter rotation clumps in a Cayley graph).
- More alpha-fixed generators (ORBIT f >= 4): 10^6-10^7 holes (fixed generators span an abelian torus; c11, c14).
- Other families at (7,11) (PGL(2,53) x Z37, SL(2,49) x Z47, AGL(1,2351)): worse (c15). Frobenius groups behave like
  random groups but random S without orbits has clumps of 2, not 6, so at Δ >= 7 the orbit search on SL wins.
- Pure random sampling of orbit S (no annealing) as a search: worse than annealing per evaluation (r2/e13).

## Tools (this folder)

- haar_meta.c: haar_big0's row-rotation bitset BFS for metacyclic groups Z_q x|_r Z_k (rows = labels j, bit = r^-j a;
  left multiplication by (b,l) is a rotation); plain random S; 2 ms per evaluation at N = 1e6.
- metacheck.c: independent BFS checker for meta solution files (own indexing, explicit group law).
- haarcheck_lean.c: independent BFS checker for SL/PSL(2,p) x Z_n with two bitsets (N/4 bytes; haarcheck_gen needs
  0.75 N, haarcheck_psl ~0.72 N); push/pull monotone-ball BFS, own element index, p x p multiplication table.
- haar_sd.c: haar_big0 plus SYM=1 (inverse-closed slots), for the negative result above.
- rank11.py (model ranking), pick11.py (candidate groups with mu and gain), dloop.sh (fresh-seed loops), harvest.sh,
  update_rows.py, renice_loop.sh (autogroup scheduling: `nice` inside a card's shell does nothing across cards; the
  loop sets the autogroup nice of squad processes to +10 and of director processes to 0 or 5).

## Machine notes

- The bash cgroup is limited to 14.3 GB: a 12.7 GB haarcheck_gen run at N = 1.69e10 was OOM-killed twice while
  searches and cards ran. Big checks need a quiet window (or haarcheck_lean at N/4 bytes, slower).
- `pkill -f <pattern>` from a Bash tool call kills the calling shell when the pattern occurs in its own command line;
  use PIDs.
