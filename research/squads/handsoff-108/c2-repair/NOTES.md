# c2-repair (handsoff-108): two-move neighbourhood of the best known states

Card: `../cards.md`, section c2-repair. Seeds 108301-108399 (not used yet: the search is deterministic, no seeds).

## Tools
- `haar_c2.c` = copy of `research/d10D8/sym2/haar_sym2.c` plus `c2_twomove.inc` (included before `orbit_main`,
  called when `TWOMOVE=1`). Build: `gcc -O3 -march=native -fopenmp -o haar_c2 haar_c2.c -lm`.
- Run: `ORBIT="3 3 1" ORBW=3 TWOMOVE=1 TWOSTATE="<10 element indices, first = e>" C2K=100 C2M=2 C2SECS=3000
  ./haar_c2 10 8 1 1 8 /dev/null psl 23 97` (prod group: `prod psl 7 sl 8 7`, n = 7).
- Energy = raw uncovered + 2 * (uncovered alpha-fixed elements) (ORBW=3), as in the annealer.

## Moves (exact, no sampling)
1. single orbit replacement: every alpha-orbit of every slot (about N/3 per slot), the C2K best kept per slot;
2. pair of orbit replacements, slots a < b: all C2K x C2K pairs (distinctness checked);
3. right multiplication of two orbits by one alpha-fixed element c;
4. fixed letter e -> alpha-fixed c: all c ranked; the C2M best get moves 1-3 again.
The loop takes the best strictly improving move and restarts.

## Log
