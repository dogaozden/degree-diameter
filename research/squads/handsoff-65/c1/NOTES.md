# c1 notes (2+2 voltage lifts by groups of order 172..180, tabu)

## Setup
- Bases: `bases/a{1,2,3}.base` = 2+2 base [[a,6-a],[6-a,a]] (vertices 0,1 side 0; 2,3 side 1), made by `mkbase.py a OUT`.
  All 2+2 bases with row/col sums 6 are of this form; a=0,6 disconnected, a=4,5 equivalent to 2,1 by relabelling.
- Group tables: `tabs/sg_<order>_<id>.txt` (GAP, `gap -q -c 'ORDER:=m; OUTDIR:="tabs";' ../shared/gap_tables.g`),
  names in `.name`. Orders 171..180 exported (171:5 groups, 172:4, 173:1, 174:4, 175:2, 176:42, 177:1, 178:2, 179:1, 180:37).
- Tabu needs parallel base edges with distinct voltages, so start with `INIT=random`.
- Pipeline: `INIT=random SECS=s SEED=k shared/tabu BASE GROUP OUTSOL` -> `python3 shared/export_lift.py OUTSOL GROUP EDGES`
  -> `shared/check.sh EDGES`.
- `screen.sh SECS ORDERS...` runs tabu on every group of those orders with a=1,2,3, appends to `screen.tsv`.

## Calibration
- Cyclic groups: cost 0 at m=120,140 within a second (560 vertices, verified bad=0 with check.sh). m=160: cost 6 (a=2) in 10 s.

## Results
(see below, updated as runs finish)

### Screen 1 (SECS=5 per group x base, random start; `screen.tsv`)
- Orders 171..175 (16 groups): best cost 6 at C19:C9 (171, id 1) with base a=1; C3x(C19:C3) 10 (a=2); C43:C4 (172) 14; C29xS3 (174) 17.
- Cost 0 not reached yet. Cyclic groups are weaker than non-abelian at 171.
- Next: orders 176..180 (screen 2, auto-started after screen 1), then deep runs (`deep.sh ORDER ID BASE SECS SEED0 NSEEDS`) on the top pairs.

### Screen 2 (orders 176..180, SECS=5, a=1,2,3) done 16:12. Best per group (min over bases):
- 176 id17 C11:Q16 (= SmallGroup(176,17), the near704 group) a2: 8; 176 id25 C11xQD16 a1: 10; 176 id1 C11:C16 a1: 12;
  176 id26 C11xQ16 a1: 12; 176 id39 C22xQ8 a1: 12; 176 id40 C11x((C4xC2):C2?) a1: 12; 180 id32 C3xC6 a1: 12.
- 172 id1 C43:C4 a2: 14. 171 (calibration): C19:C9 a1: 6.
- Nothing reached cost 0 in 5 s. Queue q1.txt (60 s runs on the top 9 pairs) started 16:12 -> deep.tsv.

### Deep runs (60 s, deep.tsv). Best floor so far = cost 4 (= the near704 level: 176 id17 C11:Q16, base a2).
- 176/17 a2 seeds 1..3: 10, 4, 14. 176/25 a1: 6, 11. 176/1 a1: 8. 176/26 a1: 12. 176/39 a1: 8. 176/40 a1: 8. 180/32 a1: 22. 172/1 a2: 18.
- 171/1 C19:C9 a1 (calibration, n=684): 6 in 60 s, so 684 by a 2+2 lift not found (not a yes/no answer).
- Tabu does only ~1500 steps per minute (each step scans 9 x m moves, each a full DFS of non-backtracking walks).
- Next: q2 = 176/17 a2 seeds 11..15 x 100 s (deep2.sh keeps solutions of cost <= 6), then kdesc (exact 2-change descent) on kept solutions.

### Floor analysis (16:30-16:36)
- q2 (176/17 a2, 100 s x 5 seeds): costs 10, 10, 4, 4, 8. Solutions of cost 4 kept in sols/.
- Cost-4 solution: far pairs are only same-side pairs: (A1, fibre 60), (A1, fibre 125), (B2, fibre 45), (B2, fibre 140)
  (uncov.py). Base a2 has the side-swap symmetry A1<->B2, A2<->B1, and the misses sit on that pair.
- kdesc (exact 2-change descent) from cost 4: no improving 2-change (1.07M candidates, 37 s): a true 2-opt local minimum.
- vl (simulated annealing, T0=3 T1=0.2) on the same group: 18 after 60 s. Tabu is much better than SA here.
- param.sh: tabu parameter sweep on 176/17 a2 (default, TMIN/TMAX long and short, TABUEDGE, STALL/KICK), 3 seeds x 40 s each -> param.tsv.
