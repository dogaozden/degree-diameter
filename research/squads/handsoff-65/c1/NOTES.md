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
