# own-small round 3: shared rules (read all of it first)

## Results so far (all checked with score48 and the all-pairs checker apsp.c)

- (3,10): valid cubic bipartite graphs on **810** vertices (table 800): 5+5 lifts over two groups of order 81.
- (3,11) (new cell; census best 1,250, lab 1,080): valid graphs on **1,260** vertices: 6+6 lifts over both groups of order
  105, even the cyclic one.
- Method: joint annealing of a p+p cubic base multigraph AND its voltages (tool salift_s). Costs at (3,10): 812 cost 6,
  816 and 820 cost 4, 880 cost 20 (short runs; states are deep local minima, so many short runs with fresh seeds beat
  long pushes). (3,11) with cyclic groups: 1,300 cost 14, 1,320 cost 12, 1,440 cost 34. (3,9) at D = 9: 510 cost 8.
  Degree 4 (salift4): far ((4,8) cost 64+ at n = 2,200; (4,9) cost 224+ at n = 5,000).
Cost = #(base vertex u, lift vertex x) with dist((u,e), x) > D; 0 = valid.

## How to use CPU in this round: the director's queue (no heavy runs of your own)

Do NOT run salift or other heavy programs yourself. Append task lines to the queue; the director's dispatcher runs them
on all 4 cores, round-robin over cards, at most 14 tasks per card, and writes results back:
  `flock /home/user/degree-diameter/research/squads/own-small/runs/queue/lock -c "echo 'CARD TOOL p N id D secs seed GROUPSFILE [STARTFILE]' >> /home/user/degree-diameter/research/squads/own-small/runs/queue/tasks.txt"`
- CARD = your card id (e.g. r3x1); TOOL = salift_s (cubic) or salift4 (degree 4); secs <= 90 (CPU seconds);
  GROUPSFILE = absolute path of a table file (gap_export text format) that contains group `id` of order N;
  STARTFILE (optional) = a previous state (.sol.best or .sol) of the same N, id, p to restart from.
- Results: `grep " CARD " .../runs/queue/results.txt` lines "k CARD p= N= id= D= seed= best=<cost> n=<2pN> state=<file>".
  Cost-0 states are converted and checked with score48 automatically: `.../runs/queue/valid.txt`.
- Wait for results with foreground Bash calls of at most 8 minutes, e.g.
  `timeout 470 bash -c 'until [ $(grep -c " r3x1 " .../results.txt) -ge 5 ]; do sleep 15; done'`.
  Submit in small batches (e.g. 4-6 tasks), look at the results, then submit the next batch (evolve: restart from your
  best states with START, try neighbouring groups or orders). 14 tasks in total per card.
- Group tables: `/home/user/degree-diameter/research/squads/own-small/runs/gtxt/g<N>.txt` (all groups of order
  16..125), `.../runs/cyc/c<N>.txt` (cyclic C_N, N = 100..240, id 1). For other orders you may export tables with GAP
  yourself (short jobs only, orders <= 300 with <= 30 groups): `echo 'L:=[N1,N2];; MAXG:=30;; dir:="<your folder>";;
  Read("/home/user/degree-diameter/research/squads/own-small/tools/gap_export_fast.g");' | nice gap -q -o 4g`.
  You may also write a table of a group you construct yourself (direct or semidirect products), in the same format
  ("G N id name" then N rows of N indices, row a column b = index of a*b, identity 0).
- Work only in `research/squads/own-small/r3/<card>/`. No git writes. Time box about 60 minutes.

## Scoreboard (one JSON line per card, at the end)

Append one line to /home/user/degree-diameter/research/squads/own-small/r3/scoreboard.jsonl:
{"card": "<id>", "cell": "3,11", "idea": "<one line>", "best_n_valid": <largest valid n or 0>, "best_near": "<n and cost
of your best invalid state>", "files": "<state paths>", "next": "<one line>"}
Then reply in at most 5 lines; if valid.txt shows a VALID line from your card with n above the current best, say so first.
