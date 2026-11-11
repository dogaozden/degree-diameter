# Squad round 1, cell (12,5): preamble shared by all cards

Goal: a bipartite graph of maximum degree 12 and diameter 5 on as many vertices as possible.
- Table value 8,200. **Ours so far: 9,720 (m = 60)** (Opus: 8,748 at 19:31, 9,720 at 19:41 UTC). Beat 9,720 (m ≥ 61); then 10,692 (m = 66).
- Someone else's graph has 11,664 (double cover of Mizuno's (12,4) graph); m ≥ 73 below would beat it.

## The construction (route-chart lift; research/d12D5/README.md, research/theorems/BEAT_16_5_SQUAD.md §2)

- **Controller**: a 4-regular bipartite multigraph with m vertices per side, properly 4-edge-coloured (colours 0..3).
  We build it as a voltage lift of a small *base* (k + k vertices, 4k edges, files `base_*.txt`, `bases3/`, `bases4/`)
  by a group of order n (table files from `groups.py`), so m = k·n.
- **Chart** over F_3: matrices A_0..A_3 in GL_4(F_3), vectors b_0..b_3 in F_3^4 (text file: 4 lines of 16 entries,
  then 4 lines of 4 entries). Controller edge a–b of colour c becomes the 3·81 lift edges (a, x) – (b, A_c x + λ b_c).
- **Lift**: 12-regular bipartite, **2 · 81 · m vertices**. m = 60 → 9,720 (ours); m = 63 → 10,206; m = 66 → 10,692; m = 72 → 11,664.
- **Cost** (printed by the annealers as `best_cost`): number of uncovered (source orbit, target) controller pairs.
  **cost 0 ⇒ the lift has diameter ≤ 5** (pencil lemma + nonsingular walks), up to the independent check below.
  A walk's colour pattern can be *singular* for the chart (its 4 vectors do not span F_3^4); a chart has a 216-line
  pattern table "side i1 i2 i3 i4 rank". Over F_3 no chart makes all 216 patterns nonsingular (proved by
  `tripods.py` / `universal3.py`); the best found so far has 18 singular patterns and full pencil.

## Tools (all in research/d12D5/; binaries already compiled there, call them by path, do not rebuild in place)

| tool | usage | notes |
|---|---|---|
| `chart3` | `chart3 SECS SEED [PW] [OUT]`; `chart3 -p CHART PATTERNS.txt` | search charts (cost = singular + PW·pencil); write pattern table |
| `gf3.py` | `python3 gf3.py relabel CHART PREFIX`; `python3 gf3.py lift CTRL.edges CHART OUT.edges` | 24 colour relabellings (PREFIX_qXX.txt + PREFIX_chart_qXX.txt); build the lift |
| `groups.py` | `python3 groups.py "cyc 20" OUT`; `"dih 10"`; `"meta 7 3 2"`; `"prod cyc 2 / cyc 10"`; `"dicyc 5"` | group tables |
| `mlift_chart` | `mlift_chart BASE TABLE PATTERNS SECS SEED [T0] [OUT.edges]` | anneals voltages for a FIXED chart (pattern table); writes OUT.edges at cost 0 |
| `mlift_joint3` | `INIT_CHART=CHART mlift_joint3 BASE TABLE SECS SEED [T0] [PV] [OUTPREFIX]` | anneals voltages AND chart; writes OUTPREFIX.edges + OUTPREFIX.chart at cost 0 (or with WRITEBEST=1) |
| `apsp` | `apsp LIFT.edges 12 5` | **the scorer**: independent all-pairs check; must print `RESULT VALID d=12 D=5 n=...` |
| `sweep_rel.sh` | see the file | all 24 relabellings with mlift_chart (runs 4 at a time: do NOT use it in a squad card) |

Existing data: charts in `research/d12D5/charts/` (`c3_s1.txt` = 18 singular, pencil-complete; relabellings
`c3s1_qXX.txt` / `c3s1_chart_qXX.txt`), tables in `research/d12D5/tables/` (z14..z27).
Known results: K33m (`base_k33m.txt`, K_{3,3} + doubled perfect matching) over Z_18 (m = 54): cost 0 in seconds,
lift 8,748 VALID. Over Z_20 (m = 60) joint annealing (mlift_joint3) reached cost 0 on 1 of 5 seeds of 150 s (lift 9,720 VALID); over Z_22 (m = 66) the fixed chart gives cost 4.

**Building and checking a cost-0 controller** (do this for every cost-0 result with m ≥ 61):
- from `mlift_chart ... PATTERNS=PREFIX_qXX.txt ... OUT.edges`: `python3 gf3.py lift OUT.edges PREFIX_chart_qXX.txt lift.edges`
  (the chart MUST be the relabelled chart matching the pattern file);
- from `mlift_joint3 ... OUTPREFIX`: `python3 gf3.py lift OUTPREFIX.edges OUTPREFIX.chart lift.edges`;
- then `apsp lift.edges 12 5`. Only `RESULT VALID` counts. Keep the controller, chart and apsp output in your folder
  (delete lift.edges afterwards if it is large; it can be rebuilt).

## Machine rules (16 Haiku cards share 4 cores and 15 GB with Opus)

- At most ONE heavy process at a time per card. Always `timeout <s> nice -n 10 <cmd>`. THREADS=1. ≤ 1.5 GB memory.
- The annealers' SECS is CPU time; with 16 cards the wall time is ~4× longer. Prefer many short runs (30–120 s CPU,
  several seeds) over a few long ones: plateaus form fast and new seeds beat long runs.
- Work only in your card folder `research/squads/d12D5-r1/cK/` (write scripts and outputs there). No git commands.
  No edits outside your folder. No network unless your card says so.
- Time box: about 35 minutes wall clock, then report.

## Report

Append ONE line of JSON to `research/squads/d12D5-r1/scoreboard.jsonl` (use `>>`, one line, no pretty-printing):
`{"card": "cK", "idea": "<one line>", "code": "<path>", "command": "<exact best command>", "m": <m>, "best_cost": <int>,
"score": <lift vertices if apsp VALID else 0>, "valid": true|false, "next": "<one line>"}`
Then reply in at most 5 lines: best m with cost 0 (and apsp result), best near miss (m, cost), one-line lesson.
