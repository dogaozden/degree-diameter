# c1 notes (deep-49 round 1): non-solvable groups of order 2520 (and 2580, 2640), exact cost minima

No cost-0 Haar graph was found for any group below. Every result is exhaustive over Aut(G)-reduced sets
(hx, LIMIT as stated), so each number is exact.

## Files
- `mkgap.py`: writes `g/NAME.g` (one GAP script per group; reads `export_group_c1.g`, which is the squad's
  export_group.g with `MinimalGeneratingSet` replaced by `SmallGeneratingSet`, because MinimalGeneratingSet
  refuses non-solvable groups).
- `g/NAME.exp` (GAP export), `g/NAME.tab` / `g/NAME.aut` (built by `build_tab.py`), `g/NAME*.hits` (hit lines).
- `hx`, `build_tab.py`, `score48`, `apsp`: copies of the squad tools (not edited).

## Rerun
    cd research/squads/deep-49/r1/c1
    python3 mkgap.py && cd g && gap -q --quitonbreak NAME.g < /dev/null && cd ..
    python3 build_tab.py g/NAME.exp g/NAME
    ./hx g/NAME.tab g/NAME.aut 0 9 1 99999 g/NAME.hits      # LIMIT 0 (all x reps)
    # split with XFROM XTO when a run is long; each chunk: MIN c (exact min in chunk when c <= LIMIT)

## Results (exact minimum over all Aut-orbit representatives; x-orbit counts from hx stderr)
| group | order | x-orbits | result |
|---|---|---|---|
| A7 (calibration) | 2520 | 7 | 6 (LIMIT 5 gives MIN >5, LIMIT 6 chunks give 6; matches the known 6) |
| A6 x C7 | 2520 | 9 | 8 (LIMIT 6 > 6; LIMIT 8 chunks 1-4, 5-9 both MIN 8) |
| PSL(2,7) x C15 | 2520 | 19 | 10 (LIMIT 8 > 8; LIMIT 10 chunk 1-9 MIN 10; chunks 10-19 at LIMIT 9 > 9) |
| SL(2,5) x (C7:C3) | 2520 | 27 | 4 (LIMIT 4 chunks 1-9, 10-18, 19-27 all MIN 4) |
| SL(2,5) x C21 | 2520 | 27 | >10 (LIMIT 10 chunks 1-13, 14-27 both >10) |
| A5 x (C7:C6) | 2520 | 27 | >10 (LIMIT 10 chunks 1-13, 14-27 both >10) |
| A5 x C42 | 2520 | 31 | >10 (LIMIT 10 chunks 1-16, 17-31 both >10) |
| A5 x D21 (order-42 dihedral) | 2520 | 19 | >10 (LIMIT 10 full >10) |
| A5 x C3 x D7 | 2520 | 23 | >10 (LIMIT 10 full >10) |
| A5 x C2 x (C7:C3) | 2520 | 31 | 9 (LIMIT 10 chunk 1-16 MIN 9; LIMIT 9 chunk 17-31 MIN 9) |
| S5 x C21 | 2520 | 27 | 7 (LIMIT 8 chunks 1-14, 15-21, 22-27 all MIN 7) |
| A5 x C43 | 2580 | 7 | >10 (LIMIT 10 chunks 1-4, 5-7 both >10) |
| PSL(2,11) x C4 | 2640 | 20 | >8 (LIMIT 8 chunks 1-10, 11-20 both >8; no LIMIT 10 run) |
| PSL(2,11) x C2 x C2 | 2640 | 13 | >10 (LIMIT 10 chunks 1-6, 7-13 both >10) |

Cost-0 search (LIMIT 0, full x range) was MIN >0 for all 13 targets.

## Notes
- The Aut generators come from GAP's AutomorphismGroup (via export_group). hx stays exhaustive for any subgroup of
  Aut(G), so the reduction is exact even if the generators are not a full generating set.
- Machine load varied: a LIMIT 6 chunk of PSL(2,7) x C15 (reps 10-19) once hit the 100 s limit, and was rerun in
  smaller chunks.
- Runtime per run: LIMIT 0 is 1-25 s for all groups; LIMIT 8 is 10-60 s per full group.
- Scoreboard: the first c1 lines for the >8 groups are superseded by the UPDATE lines (>10), and the A5 x C2 x (C7:C3)
  and PSL(2,7) x C15 lines by the 9 and 10 lines. One UPDATE line names A6 x C7 by mistake; its code field is SL(2,5) x C21.
