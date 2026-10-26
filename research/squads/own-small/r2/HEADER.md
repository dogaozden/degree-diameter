# own-small round 2: shared rules for every card (read all of it first)

Job "own-small" (Oct 26 2026). Bipartite degree-diameter problem: a bipartite graph with maximum degree d and diameter
<= D on MORE vertices than the table. Cells: (3,10) > 800, (3,9) > 506, (4,8) > 2,184, (4,9) > 4,970.

## The lead from round 1: it already worked

Joint annealing of a p+p cubic base AND its voltages (tool salift) found two VALID (3,10) graphs on 810 vertices
(table 800), checked with score48 and the all-pairs checker: 5+5 lifts over SmallGroup(81,12) = C3 x ((C3xC3):C3) and
SmallGroup(81,9) = (C9xC3):C3, each after 45 s of CPU (research/squads/own-small/records/). In the same 45 s screen,
5 more groups of order 81 reached cost 2-4. Both winners are 3-groups. **Round 2's goal: valid (3,10) graphs with
n > 810, as large as possible** (and the same method at (3,9) and, with a degree-4 version, at (4,8)/(4,9)).
Cost = #(base vertex u, lift vertex x) with dist((u,e), x) > D; far pairs = cost * N / 2.
Strategy for every slot: screen all groups of the smallest order first; as soon as some group reaches cost 0 at an
order, check it with score48, save it, and move up to the next order; report the largest valid n you reached.

## Machine rules (4 cores shared by 16 cards and the director)

- ALL heavy computation goes through the CPU gate, as ONE job script per card: write `job.sh` in your folder that does
  your whole plan (screen + push), then run `$T/slot.sh 900 bash job.sh` ONCE (at most 900 s of CPU; a second gated
  job of <= 600 s only if the first one finished early and you have a strong reason). The gate gives the job a whole
  core; it may wait in the queue first, so start it early. Never run anything heavy outside the gate, never use `&`.
- Do NOT run GAP: the group tables you need are already exported (below). Single-threaded, <= 1 GB memory.
  No git writes. Work only in `research/squads/own-small/r2/<card>/`. Time box: about 60 minutes wall time.

## Tools (T=/home/user/degree-diameter/research/squads/own-small/tools; binaries in $T/bin)

- `$T/bin/salift_s2 p GROUPS id seed seconds T0 T1 OUT.sol` with env `D=10` (or 9): joint base+voltage annealing of a
  p+p cubic bipartite base (p <= 32) over group `id` of the table file GROUPS. Prints "t=.. it=.. best c" lines and
  "end best c its ..". Writes OUT.sol.best (first line "N id p cost", then 3p lines "u v a") whenever the best improves,
  and OUT.sol at cost 0. Env `START=file.best` starts from a saved state (same N, id, p) instead of a random one.
  Defaults that worked: T0 = 10, T1 = 0.3 (the temperature cycles every 30 s of CPU). `seconds` is CPU seconds.
- Group tables (all groups of each order, gap_export text format "G N id name" + N rows, identity 0):
  `/home/user/degree-diameter/research/squads/own-small/runs/gtxt/g<N>.txt` for N = 51..125.
- `python3 -I $T/best2edges.py GROUPS.txt STATE OUT.edges` turns a .best/.sol state into an edge list.
- **Scorer (the only one that counts):** `$T/bin/score48 EDGES 3 10` (args d D); last line "RESULT VALID n=..." or
  "RESULT INVALID n=... far=...". For degree 4: `$T/bin/flift` / `$T/bin/lift` (see their headers), score48 EDGES 4 8.

## Already found / already ruled out (do not redo)

(3,10), table 800:
- No cubic vertex-transitive graph up to 1,280 vertices (best 768) and no edge-transitive one up to 10,000 (best 720).
- 2+2 lifts over EVERY group of order 200..250: none (minimum cost 2, e.g. n = 880, SmallGroup(220,2)).
- Covers of the Tutte 12-cage (cost > 3,000), 4+4 fixed-base flift lifts over 159 groups of order 101..125 (best cost 8
  at n = 864, short runs), semi-edge 2-vertex bases (cost 5 at 812), 7+7 over order 60 (n = 840, 1,320 far pairs),
  symmetry-breaking re-annealing of the 880 near miss (no move), delete-and-rematch surgery (no move).
- Director (do not redo): cubic Haar graphs and stabiliser-2 bi-coset graphs over all groups; 5+5 over all 15 groups of
  order 81 (n = 810, done: two valid); 6+6 over all 15 groups of order 81 (n = 972, runs/p6/).
(3,9), table 506 (a Haar graph of Z23:Z11): no VT graph on 508..1,280 vertices; 2+2 lifts of all groups of order
  127..160 and Haar graphs of all groups of order 254..511 are the director's (do not redo).

## Scoreboard (one JSON line per card, at the end)

Append exactly one line to /home/user/degree-diameter/research/squads/own-small/r2/scoreboard.jsonl:
{"card": "<id>", "cell": "3,10", "idea": "<one line>", "code": "<path>", "command": "<exact command for the best
file>", "n": <vertices>, "cost": <salift cost or far pairs, say which>, "valid": true|false, "check": "<score48 RESULT
line>", "files": "<best state and edge list paths>", "next": "<one line>"}
Then reply to the director in at most 5 lines; if score48 says VALID with n above the table, say so in line 1.
