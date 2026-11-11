# r2d auditor notes (deep-49 round 2)

## 1. Code review of tools/hx.c (exact Haar search, Aut-reduced)
Read in full. Reasoning checked:
- S = {e,x,y,z} with e in S is WLOG (left/right translation of S gives isomorphic H(G,S)).
- x = Aut-orbit representative: any s in S\{e} maps to the representative by some automorphism (the group generated
  by the AUT list), and that automorphism fixes e. Sound for any subgroup of Aut(G), so an incomplete AUT list is harmless.
- (y,z): y over Stab(x)-orbit reps on G\{e,x}, z over all z with orbit index >= that of y. For a pair {y0,z0} with
  orbit indices a <= b, a stabiliser element maps y0 to rep_a and z0 to an element of index b >= a. Covered. Sound.
- Stabiliser: Schreier generators from a correct transversal (each generator fixes x). Capping at 4096 generators only
  makes the subgroup smaller, which only refines orbits; still exhaustive.
- Cost: (SS^-1)^4 = X*X with X = T1*T1 (T1 = SS^-1), and the killer lower bound c > lim is a count of distinct missed
  elements. Both sound. The miss_full early exits return values > lim only when the partial count already exceeds lim.
- Diameter criterion: diam <= 9 iff (SS^-1)^4 = G and (S^-1 S)^4 = G (checked by argument).

Doubts (none triggered by the runs that were certified, none found to be wrong):
1. D1 (latent): `if (nx*nx < N) return lim+1;` rejects a set when |X|^2 < N. The true cost is then >= N - |X|^2 >=
   N - floor(sqrt(N-1))^2, so the rejection is only sound while LIMIT < N - floor(sqrt(N-1))^2. For the orders used:
   2520 -> 20, 2525 -> 25, 2496 -> 95, 2485 -> 84, 4970 -> 70. All runs used LIMIT <= 10 (or 8), so unaffected.
2. D2 (checked here): AUT generators are only checked on 2000 random pairs. Full N^2 check (check_aut.py) passes for the
   SL25x_C7C3 and g104 generator files. Other .aut files were not checked.
3. D3 (process): a chunk printing "MIN >L" only says something about its own range XFROM..XTO; the aggregator must
   cover reps 1..nrep-1. The ranges listed in r1/c1/NOTES.md cover all reps for each group.
4. D4 (process): the table is trusted to be a group with identity 0 (setup_inv checks identity and inverses only).
   Random associativity (2e6 triples) passes for SL25x_C7C3.

## 2. Independent code: handsoff exh3.c (copied to ./exh3.c, from
   origin/claude/handsoff-49-bipartite-search-hy5axz:research/squads/handsoff-49/w11/exh3.c)
Uses left multiplication edges and its own symmetry (automorphisms from verified maps with pair-marking, or inner
automorphisms for tables) and its own bitset BFS. Read it in full; the argument for exhaustiveness holds (each pair
is either evaluated or is an image of an evaluated pair under an automorphism fixing e and x). Cost values agree with
hx's convention (the same cost for the same set).
- ./exh3m = exh3.c plus an optional MUST filter (env MUST=g,...; the set counts only if g is at distance <= 8 from both
  roots) and HITMAX (env). Built by patch_must.py. The program aborts if an automorphism in the list moves a must element.

## 3. Re-checks (scoreboard lines in r2/scoreboard.jsonl, card "r2d")
| claim | run | result |
|---|---|---|
| (a) Z71 x| Z35 (record) has a cost-0 Haar set | exh3 meta 71 35 49 0 rec71 (35 reps, 24 cost-0 hits) | confirmed; witness S={0,71,285,1248}; apsp: VALID at D=9 (n=4970, deg 4, bip), INVALID at D=8 |
| (b) Z101 x| Z25 minimum 2 | exh3 meta 101 25 5 2 z101 (25 reps) | confirmed: min 2, 48 cost-2 hit lines (hx in c4: 48 cost-2 reps); python witness {303,708,1564} cost 2 |
| (c) SL(2,5) x (C7:C3) minimum 4 | exh3m tab .../SL25x_C7C3.tab 4 sl25 (44 inner-class reps) | confirmed: min 4, only cost-4 lines |
| (d) D2494 has no cost-0 Haar set | exh3m meta 1247 2 1246 0 d2494 | confirmed (4 reps, no hit) |
| (d) D2514 has no cost-0 Haar set | exh3m meta 1257 2 1256 0 d2514 | confirmed (4 reps, no hit) |
| (d) D2518 has no cost-0 Haar set | exh3m meta 1259 2 1258 0 d2518 | NOT FINISHED: one representative takes over 100 s and exh3 saves state per representative |
| (e) Z104 x|_7 Z24, 52 covered on both sides: min 8 | MUST=52 HITMAX=8 exh3m meta 104 24 7 8 m104z (67 reps, 35 s) | confirmed: min 8, 96 hit lines all cost 8; python witness {104,313,1198} cost 8 with must_ok |
| (e) calibration: unconstrained Z104 x|_7 Z24 min 4 | exh3m meta 104 24 7 4 u104 | confirmed: min 4 |
| hx AUT files | check_aut.py on SL25x_C7C3 and g104 | all generators bijective automorphisms |

Random group pick for (d): python random.Random(49).sample over unambiguous descriptions (pick_d.py). The groups were
identified by the survey description only (dihedral groups are unique by name). D2494 and D2514 were rebuilt by
exh3m's own meta construction, not by mkmeta.py.

## 4. Observations on round-1 and round-2 files (not re-checked)
- r2/cards.md, r2a says PSL(2,7) x C15 "> 8"; r1/c1/NOTES.md gives 10 (LIMIT 10 chunk 1-9 MIN 10). Card text is stale.
- r1/c1/NOTES.md says one UPDATE scoreboard line names A6 x C7 but has the code field of SL(2,5) x C21.
- Hit-line counts depend on the reduction (c4's 184 cost-4 sets vs 96 hit lines here for the same group); only the
  minimum is comparable.

## How to rerun
    cd research/squads/deep-49/r2/d
    gcc -O3 -march=native -o exh3 exh3.c && gcc -O3 -march=native -o exh3m exh3m.c
    mkdir -p state hits out
    ./exh3m meta 71 35 49 0 rec71 60 9
    python3 witness.py 71 35 49 71,285,1248 rec71_w0_py.edges && ../../tools/apsp rec71_w0_py.edges 4 9
    ./exh3m meta 101 25 5 2 z101 60 9
    ./exh3m tab /home/user/degree-diameter/research/squads/deep-49/r1/c1/g/SL25x_C7C3.tab 4 sl25 60 9
    MUST=52 HITMAX=8 ./exh3m meta 104 24 7 8 m104z 70 9
