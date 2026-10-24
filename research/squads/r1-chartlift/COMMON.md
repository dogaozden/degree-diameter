# Squad r1-chartlift: shared brief (read fully, ~3 minutes)

You are one of 8 Haiku agents in a research lab on the bipartite degree-diameter problem: build a bipartite graph of
maximum degree D and diameter 5 with as many vertices as possible. Repo: /home/user/degree-diameter. Tools:
research/theorems/chartlift/ (read its README.md first). Work ONLY inside your card folder
research/squads/r1-chartlift/cN/ (create it; copy tools there if you modify them). No git commands. Don't edit
anything outside your folder except appending your one scoreboard line.

Machine: 4 cores shared by 9 agents. Run at most ONE heavy process at a time, single-threaded. Prefix heavy
commands with `timeout 900 nice -n 10`. Memory < 1.5 GB. Delete *.edges files after checking them.
Compile tools once in your folder: `gcc -O2 -o ctrl_search ../../../theorems/chartlift/ctrl_search.c -lm` (same for
apsp.c, chart_anneal.c). Python scripts are run from research/theorems/chartlift/ (they import each other), e.g.
`cd /home/user/degree-diameter/research/theorems/chartlift && python3 lift.py ...`.

The construction ("route-chart lift"): a controller C (k-regular bipartite, properly k-edge-coloured, m vertices per
side) and a chart (matrices A_c, vectors b_c over the field F_q, fibre F_q^4). Lift: vertex (u, x), x in F_q^4; a
controller edge u--v of colour c gives (u, x) ~ (v, A_c x + lam b_c) for lam in F_q. The lift has degree k*q and
2*m*q^4 vertices. Controllers here are voltage lifts of a small base multigraph by a group; `ctrl_search` anneals the
voltages; its cost counts controller pairs that the chart fails to connect; **cost 0 means the lift has diameter
<= 5**, which you then confirm by building the lift and running the all-pairs checker:
  cd research/theorems/chartlift
  python3 lift.py <your>.ctrl <chart>.txt q k /tmp/<card>.edges
  <your folder>/apsp /tmp/<card>.edges DELTA 5          # must print RESULT VALID
A ctrl_search run: `./ctrl_search BASE GROUP FLAGS SECONDS SEED OUTPREFIX` (SECONDS is wall-clock; use 60-300).
BASE files: research/theorems/chartlift/bases4/*.txt, bases5/*.txt, bases_k33m_col.txt (K3,3 + doubled matching with
colours). GROUP: `cyclic:N` or a table made by `python3 groups.py dih:10 <folder>/dih10.txt` (see groups.py doc).
m = r * |G| where r = first number in the base file.

Current records (lift sizes): (12,5): table 8,200, ours 8,748 (k=4, q=3, K3,3+matching over Z18, m=54).
(8,5): table 1,710, lab 1,764; ours 1,728 (k=4, q=2, m=54). (16,5): ours 33,792 (k=4, q=4, m=66).
(15,5): table 20,496. (10,5): table 4,000.

When done (time box ~20 minutes of work), append ONE line of JSON to
research/squads/r1-chartlift/scoreboard.jsonl:
{"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact command reproducing your best>",
 "score": <best m with cost 0, or best lift size>, "valid": true|false, "next": "<one line>"}
"valid" is true only if apsp printed RESULT VALID for that lift. Then reply in at most 5 lines.
