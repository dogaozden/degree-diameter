# c26 notes (card: "1,6|1,6"-type coset graphs with NON-CYCLIC hub stabilisers, orders 294..312)

## Model (same block structure as c18, N = 5,1,1,0)
G acts by right multiplication. A0 = G, A1 = G/H, B0 = G, B1 = G/K, |H| = |K| = 6, H and K any subgroups of order 6
(C6 or S3). n = 7|G|/3 (686 for |G| = 294). Blocks: S = 5 elements (A0-B0: x ~ s^-1 x), g01 (A0-B1: x ~ coset K(g01^-1 x),
one edge), g10 (A1-B0: coset Hx ~ inv(h g10) x for h in H, six edges); no A1-B1 block. Degrees are checked in build().
Diameter: the four representatives (A0 identity, A1 coset of 1, B0 identity, B1 coset of 1) must reach everything in 5
steps; cost = sum over the 4 representatives of far vertices (the same scale as c18's t18 and mcos).

## Tools
- subs.g: GAP, lists all subgroups of order 6 of SmallGroup(ORDER,i) with type C6/S3, indexed like c18/groups tables.
  Output in c26/subs/sub6_ORDER_i.txt (e.g. `gap -q -c 'ORDER:=294; OUTDIR:="subs";' subs.g`).
- t26.c (gcc -O3 -march=native -o t26 t26.c -lm): tabu over S, g01, g10, H, K (full neighbourhood, bitmask all-pairs
  propagation for the 4 representatives, about 21 us per evaluation). Usage:
  `t26 TABLE SUBS HT KT SEED TLIM TENURE OUT` with HT, KT in {C6, S3}; env HIDX/KIDX fix start, FIXHK=1 freezes H, K.
  Writes OUT (edge list) at every new best; stops at cost 0 and prints CLAIM.
- Groups: c18/groups/sg_ORDER_i.txt tables (c18 generated them).

## Results
- Calibration (cyclic, c18's 294_11, C6 C6): seed 8, 240 s -> cost 5 (c18's t18 reached 2 in 144 s with its own moves).
- S3|S3 screen, 50 s each, seed 1, tenure 12:
  294_3 166, 294_5 176, 294_20 200, 294_21 69, 294_22 158, 294_7 13 (294_7 = (C7xC7):S3, 49 S3 subgroups).
  294_3, 294_5, 294_20, 294_21, 294_22 have few or structurally bad S3 hubs at this budget.
