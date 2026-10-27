# omega_repair: relabelling the copies of Gómez's ΩH_q (job thm-omega-repair)

Theory note: `research/theorems/OMEGA_REPAIR.md`. Everything below is from scratch except `hexq6.c` (copied from
branch claude/own-12-8-cell-ig5jhd, research/d12D8/omega/) and `check/omega_model.h`, `check/omega_eval.c` (copied
unchanged from claude/table-audit-2-p7x6hn, research/projects/table-audit/omega/, used only as an independent check).

## Build

    cc -O2 -o hexq6 hexq6.c && for q in 2 3 4 5 7; do ./hexq6 $q hex_q$q.txt; done
    cc -O2 -march=native -fopenmp -o twist twist.c -lm
    cc -O2 -march=native -fopenmp -o tanneal tanneal.c -lm
    cc -O2 -fopenmp -o routecount routecount.c -lm
    cc -O2 -o routecount2 routecount2.c -lm
    cc -O2 -o counts counts.c
    cc -O2 -fopenmp -o routes_dump routes_dump.c -lm
    cc -O2 -o check/omega_eval check/omega_eval.c

## Programs

| file | what |
|---|---|
| `geo.py` | GF(q), H(q) coordinates (hexq6 format), collineation check of a 7x7 matrix, SL(3,q) embedding, long root elations |
| `mktwist.py` | twist files: `id` (thesis), `rand` (random elements of G₂(q)) |
| `structured.py` | twist files: Singer powers, arithmetic Singer powers, one root group, two root groups |
| `gens.py` | generator pool for the annealer |
| `twist.c` | ΩH_q, reading 2, twisted copies: `formula` (exact far pairs from the route balls, Lemma 2.1), `bfs` (explicit graph, bit-parallel BFS from hubs or `all` vertices), `edges` (edge list). `TSTEP=k` samples every k-th row |
| `tanneal.c` | annealing over the twists, cost = `formula` |
| `routecount.c` | route numbers m₄, m₂ per (hub class, missed copy) for reading 2, every a/b pattern; the bound q⁵ − m₄q⁴ − m₂q² |
| `routecount2.c` | the same from a separate search over free-group words, any reading and inner classes, dualities allowed; `sweep A1 A2` for reading 2 over α |
| `counts.c` | Lemma 3.1's constants on H(q), points and lines |
| `routes_dump.c` | per (hub class, missed copy): numbers of radius-4 and radius-2 centres (the q = 7 starved pairs) |
| `overlaps.py` | Lemma 4.1's overlap bounds, sampled |
| `degen.py` | Lemma 4.3: the 17 degeneracy structures at q = 7, their Bonferroni bounds and forced perpendicular pairs |
| `degen_check.py` | Lemma 4.3 checked against exact unions on 4,000 constructed configurations in H(7) |
| `perpbound.py`, `fpfperp.py` | Lemma 4.4: eigen-kernel dimensions, the bound and the true |Perp(h)| for fixed-point-free h ∈ G₂(7) |
| `genpos.py` | how many points t are in general position for a starved pair (random twists, q = 7) |
| `polar.py` | labellings by quadric isometries / collineations / random bijections, for `check/omega_eval` (Computer-checked 5.1) |
| `siegel_check.py`, `perpfrac.py` | which Siegel transformations are collineations; how often g(t) ⊥ t |
| `check/tolab.py` | converts a twist file to the audit's labelling format, for `check/omega_eval` |

## Reproduce the main numbers

    ./routecount2 sweep 3 9                 # Theorem 3.3 / Computer-checked 3.4
    ./routecount2 total 9 6                 # lower bounds on all far pairs
    python3 degen.py; python3 perpbound.py 400 3; ./routes_dump hex_q7.txt aabbb   # Theorem 4.5 ingredients
    for qa in "8 5" "9 6" "11 7" "13 8"; do ./routecount2 $qa all; done      # Theorem 3.5
    python3 mktwist.py hex_q4.txt 15 q4.bin rand 1 && ./twist hex_q4.txt q4.bin aba formula   # 18,464,523
    ./twist hex_q4.txt q4.bin aba bfs       # same count by BFS
    python3 check/tolab.py hex_q4.txt q4.bin aba chk && ./check/omega_eval chk.hex aba PLP chk.lab 8 hubs  # same, audit code

Logs of every run quoted in the note are in `logs/`.
