# Squad c157b-r2 (job cell-15-7, resume session, 2026-10-25): common brief

## Goal
Raise the (15,7) record held on our branch: **2,501,008** (table 2,480,184). The graph is seven levels of the incidence
graph of the generalized hexagon H(11) plus hubs: n = 14 * 177,156 + KB + KA, with
  KB = min(|P0|, |P1|) + 1,536 and KA = min(|S3|, |S4|) + 1,536 (after the pairs that cannot be served are dropped).
P0, P1 are sets of POINTS of H(11), S3, S4 sets of LINES. Unlike a plain non-collinear set, each may contain PAIRS:
every element may be collinear (points) / concurrent (lines) with AT MOST ONE other element of its set (the collinearity
graph on the set is a matching). Pairs are allowed only for "allowed" elements (coverage masks, see below), and each pair
costs hub constraints, which can fail; failing pairs lose one element. Read research/d15D7b/RELAXED.md (why pairs are
allowed) only if you need the theory; the scorer below does all the bookkeeping.

## Data (research/squads/c157b-r2/shared/; copy what you change into your own folder)
- hex_q11.bin: H(11) (format: research/squads/c157b-r1/COMMON.md). Every point is on 12 lines, every line has 12 points.
- P0.txt, P1.txt (about 9,055 points each), S3.txt, S4.txt (about 8,690 lines each): the current best bottleneck sets.
- allow_P2.txt / allow_S2.txt: the coverage masks for the CURRENT sets: a point may have a partner only if it is in
  allow_P2 (it lies on a line of S3 u S4 u sigma(R')); a line only if it is in allow_S2 (it meets a point of P0 u P1 u R').
  So the masks of P depend on S and vice versa: `python3 shared/mkmasks2.py P0 P1 S3 S4` rewrites both (in the cwd).
- Pfree_unmasked.txt: a 9,306-point set with pairs but NO mask (shows what is possible without coverage limits).
- RH.txt, RL.txt: the best plain sets (8,645 non-collinear points, 8,246 non-concurrent lines); RHb, RLb: images.
- research/d15D7b/dpack.c: the ILS used so far (force-insert + greedy refill). Build: gcc -O2 -o dpack dpack.c.
  `./dpack HEXBIN P|L SEED SECONDS START.txt ALLOW.txt 0 OUT.txt` (prints 'best <size> ... violations 0').
  From P0.txt with allow_P2 it gains slowly; without a mask it reached 9,306 in 10 minutes.
- shared/chkset.py is NOT the right checker here (it forbids pairs); dpack verifies (R1) itself, and the scorer checks all.

## Scorer (exact, about 10-20 s)
  python3 research/d15D7b/score_relaxed.py research/squads/c157b-r2/shared/hex_q11.bin \
      research/squads/c157b-r2/shared/d14D7_hex11_mirror768_n1774632.sol research/squads/c157b-r2/shared \
      P0.txt P1.txt S3.txt S4.txt WORKDIR
prints `SCORE n = ...`. It designs the other friendly sets, assigns hubs, drops unservable pairs (the final sets are left in
WORKDIR/P0.txt etc.). Current: about 2,501,000. Score your four sets (copy the shared ones for the sets you do not change).

## Rules (shared machine: 4 cores, 15 GB, shared with 5 other cards and Opus)
- Work ONLY in research/squads/c157b-r2/<card>/. No git commands. No edits elsewhere.
- ONE heavy process at a time per card, single-threaded, prefixed with `timeout 1200 nice -n 10`. At most 1.5 GB memory.
- Time box: about 30 minutes wall time in total.
- Keep your best four sets as <card>/best_P0.txt, best_P1.txt, best_S3.txt, best_S4.txt (the scorer's WORKDIR output
  after drops is fine).
- At the end append ONE line of JSON to research/squads/c157b-r2/scoreboard.jsonl:
  {"card": "c3", "idea": "<one line>", "code": "<path>", "command": "<exact scorer command>", "score": <n>,
   "valid": true|false, "next": "<one line>"}
  and reply in at most 5 lines.
