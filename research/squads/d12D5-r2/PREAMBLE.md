# Squad round 2, cell (12,5): preamble shared by all cards

Goal: a bipartite graph of maximum degree 12 and diameter 5 on as many vertices as possible.
**Record: 10,692 (ours, m = 66).** Beat it: any VALID lift with m ≥ 67 (68 → 11,016, 69 → 11,178, 70 → 11,340,
72 → 11,664, 75 → 12,150, 76 → 12,312, 78 → 12,636, 80 → 12,960).

## Construction (read research/d12D5/EDGECHART.md first)

Route-chart lift: a 4-regular bipartite controller (m + m vertices) = voltage lift of a small base multigraph
(k + k vertices, 4k edges) by a group of order n (m = k·n); fibre F_3^4; every BASE edge e has its own letter (A_e, b_e)
(a "per-edge chart", file format `.echart`: one line per base edge, 16 entries of A_e row-major then 4 entries of b_e).
Lift: (a, x) ~ (b, A_e x + λ b_e), λ ∈ F_3: 12-regular, bipartite, 2·81·m vertices.
Annealer cost = uncovered (source orbit, target) controller pairs; cost 0 ⇒ diameter ≤ 5 (then check with apsp).

**New since round 1 (the reason for this round).** Round 1 showed the last failures are the diagonal pairs (u, u).
Opus built charts that make every diagonal pair free (closed backtracking walks cover the fibre; "backtrack-complete")
and are also pencil-complete, with only 8 singular walks per base vertex (48 of 648 on K33m): files
`research/d12D5/diag/bt*_<base>_<t>.echart` (K33m: bt_k33m_0..3, bt2_k33m_0..2, bt3_k33m_0..2, bt4_k33m_0..2;
also bt_base_k1_*, bt_base_k2_{1,2,3}_*, bt_k3_000_*, bt_k3_002_*, bt_k4_012_*, bt_base_k44_*). More can be made with
`python3 research/d12D5/diag/csp2.py BASE NSOL SEED OUTPREFIX` (about 10–60 s).
With DIAGBT=1 the annealer counts those diagonals as covered. Keep the chart FIXED (PV = 1.0, voltage moves only) or
nearly fixed (PV = 0.97): random chart moves destroy the backtrack-completeness (round-1 runs with PV = 0.85 did).

## Tools (research/d12D5/, binaries compiled; call by absolute path /home/user/degree-diameter/research/d12D5/...)

| tool | usage |
|---|---|
| `mlift_ejoint2` | `WRITEBEST=1 DIAGBT=1 INIT_ECHART=CHART [INIT_VOLT=v0,v1,..] mlift_ejoint2 BASE TABLE SECS SEED [T0] [PV] [OUTPREFIX]` → prints `best_cost=...`, writes OUTPREFIX.edges ("a b e") and OUTPREFIX.echart. `PRUNC=1` prints the uncovered pairs of the final state. `FAKE=1 DIAGBT=1` = controller ceiling (all walks/pencils/diagonals good; never build a lift from it). |
| `elift.py` | `python3 elift.py OUTPREFIX.edges OUTPREFIX.echart lift.edges` |
| `apsp` | `apsp lift.edges 12 5` → must print `RESULT VALID d=12 D=5 n=...` (the scorer; 0.1 s) |
| `echart` | `echart BASE -p CHART out.txt` → singular walks / pencil failures / missing diagonal points of a chart |
| `groups.py` | `python3 groups.py SPEC OUT`: `cyc N`, `dih N` (order 2N), `meta M K R` (needs R^K ≡ 1 mod M), `dicyc N`, `prod S1 / S2`, `perm g1;g2` |
| bases | `base_k33m.txt` (k=3, the record's base), `base_k1.txt` (k=1: 4 parallel edges, Haar controller), `base_k2_{1,2,3}.txt`, `bases3/k3_00*.txt`, `bases4/k4_0*.txt`, `base_k44.txt` |
| tables | `tables/z14.txt` .. `z33.txt` (cyclic) |

Round-1 facts: K33m over cyclic groups beats non-cyclic ones; with the old (diagonals need 4-cycles) criterion the
best real result at m = 69 was cost 4; the new chart gave cost 2 at m = 69 in one 300 s run.

## Rules

- Work only in your card folder `research/squads/d12D5-r2/cK/`; no git; no edits elsewhere; no `pkill -f`/`killall`.
- ONE heavy run at a time: `timeout <s> nice -n 10 <cmd>`; SECS is CPU seconds, wall time is 2–3× longer on the
  shared machine (4 cores). Prefer 60–200 s runs and several seeds/charts.
- Any `best_cost=0` with m ≥ 67: build the lift, run apsp, keep controller + echart + apsp output in your folder, and
  say so in the FIRST line of your reply. Delete lift.edges after checking.
- Time box about 40 minutes. Then append ONE JSON line to `research/squads/d12D5-r2/scoreboard.jsonl`:
  `{"card": "cK", "idea": "...", "code": "...", "command": "<best command>", "m": <m>, "best_cost": <int>, "score": <162*m if apsp VALID else 0>, "valid": true|false, "next": "..."}`
  and reply in at most 5 lines.
