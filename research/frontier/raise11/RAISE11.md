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
