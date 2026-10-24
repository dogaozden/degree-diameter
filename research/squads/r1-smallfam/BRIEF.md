# Squad round r1-smallfam (thm-smallfamilies session, 2026-10-24): beat (4,8) or (4,9)

## Goal
A bipartite 4-regular graph of diameter 8 with more than 2,184 vertices, or of diameter 9 with more than 4,970.
For a Haar graph H(G,S) (|S| = 4, vertices 2|G|) that means |G| >= 1093 at D = 8, or |G| >= 2486 at D = 9.

## What is already known (do not repeat)
- (4,7) was just beaten with Haar graphs of three groups of order 432:
  - Heis(F_9) x| C16 = SmallGroup(432,233);
  - (C3 x C3) : (C2 . S4) = SmallGroup(432,247);
  - (C2 x C2) : ((C9 : C3) : C4) = SmallGroup(432,249).
  Affine-type and Heisenberg-type groups work.
- Exhaustively negative at (4,8):
  - every Z_p x| Z_k (p prime), N = 1093..1870 (best cost 8);
  - every F_q x| C_k (q a prime power), N = 1093..1700 (best cost 4 at F_49 x| C_24, N = 1176);
  - AGL(3,2) (cost 43).
- PSL(2,13) (N = 1092): annealing reaches cost 8.
- At (4,9): Loz's 4970 is the Haar graph of Z71 x| Z35 (unique there). The squares groups Z_p x| Z_(p-1)/2 for
  p = 79, 83 fail.

## Tools (repo /home/user/degree-diameter, folder research/theorems/smallfam, all compiled)
- **Exhaustive Haar search up to Aut(G)** for any group given as a GAP expression:
  `python3 named.py 4 8 "EXPR" ["EXPR2" ...] --threads 1 --outdir /home/user/degree-diameter/research/squads/r1-smallfam/cX`
  - It writes `named_d4D8.tsv` with one line per group: `... DONE tested T solutions K best_cost C ...`.
  - It writes solutions to `named_d4D8_sols/`.
  - At odd D (D = 9) a best_cost above N means "(best_cost − N) uncovered in the first BFS".
  - EXPR may be:
    - any GAP group expression: `SmallGroup(n,i)`, `DirectProduct(G,H)`, `SemidirectProduct(...)`,
      `ExtraspecialGroup(27,3)`, `PSL(2,8)`, ...;
    - `Aff(n,q,H)`, the affine group F_q^n x| H for a matrix group H <= GL(n,q), for example
      `Aff(2,5,SL(2,5))` = ASL(2,5).
  - A group whose plan is too big prints `too-big`; then use annealing.
  - Typical cost: a group of order ~1300 with a large automorphism group takes ~1 minute.
- **Annealing** for matrix and metacyclic groups times Z_n:
  `/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad/haar_gen3 4 8 SECONDS SEED 8 OUTFILE GROUP... n`
  - GROUP = `sl q` | `psl q` | `pgl q` | `agl1 q` | `meta m k r` | `prod G1 G2` (q a prime or a prime power).
  - The group is GROUP x Z_n.
  - It prints a RESULT line with best cost. 0 means it found a graph and wrote OUTFILE.
- **Verification** (required before claiming valid=true):
  - For a named.py solution:
    `python3 named_edges.py "EXPR" OUT.edges i1 i2 i3 i4` (the indices of the SOL line), then
    `./verify/apsp OUT.edges 4 8`, which must print `RESULT VALID`.
  - For a haar_gen3 solution:
    `python3 /home/user/degree-diameter/research/frontier/build_haar2.py OUTFILE`, which must exit 0.

## Rules
- 4 cores and 15 GB are shared by all of you and the main session, so:
  - pass `--threads 1` and set THREADS=1;
  - prefix heavy commands with `timeout 900 nice -n 10`;
  - use at most about 1.5 GB of memory.
- Time box: 15 minutes of wall clock.
- No git commands. Do not edit anything outside your card folder `research/squads/r1-smallfam/cX/`; write your
  own scripts there.
- When done, append ONE line of JSON to `research/squads/r1-smallfam/scoreboard.jsonl`:
  `{"card": "cX", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <largest valid vertex count found, 0 if none>, "best_cost": <lowest cost seen>, "best_group": "<group>", "valid": true|false, "next": "<one line>"}`
- Reply in at most 5 lines.
