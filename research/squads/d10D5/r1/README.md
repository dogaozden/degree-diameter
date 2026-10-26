# d10D5 squad round 1 (cell (10,5); record now 4,820, ours)

Goal: a bipartite graph with max degree 10, diameter 5 and MORE than 4,820 vertices (Moore bound 14,762).

## What we have (read this first)

- The 4,800 graph (research/d10D7/DM_D5.md): Z6-lift of the incidence graph of the generalized quadrangle W(7) (400
  points, 400 lines, each on 8) plus a bijection sigma: points -> lines whose edge {p, sigma(p)} is doubled (lift
  voltages 1 and 4), flag voltages nu in {0,3}. Lift vertex (x, h) = 6x + h. Diameter 5 iff, for every same-colour
  opposite pair (distance 4 in W(7)), the 8 geodesics do not all have the same nu-parity or a "route" with a jump exists.
- Hubs (our new part, research/squads/d10D5/hubs/): "freeing" a point p deletes the 12 lift edges of p's doubled
  matching edge; then 2 hubs are joined to the fibre (p,0..5) and 2 to the fibre (sigma(p),0..5): +4 vertices.
  A hub joined to a whole fibre reaches everything within 1 + 4 = 5. What can break: (a) the freed point p must still
  reach "coset 1" of every point opposite p in 4 steps without its own jump: p - L - x - sigma(x) - u with x
  collinear with p; dually for the freed line. (b) Same-side hubs of two freed points must be within distance 4: true
  if the freed points are collinear, otherwise the hubs need a common neighbour (hub-hub edges; each hub has 4 spare
  edges since it already has degree 6). (c) the coset-0 parity condition for all pairs (fixed by annealing nu).
- Exact coverage for a freed FLAG (p on l = sigma(p)): sigma maps the 49 points collinear with p not on l onto lines
  meeting l, and the 49 lines meeting l not through p get preimages collinear with p. Several flags = a bipartite
  perfect-matching problem (hubs/flagmatch.py, hubs/flaggreedy.py). Random greedy reaches k = 5 flags; k = 6 had
  matching deficiency 2..10 in the few tries so far. Collinear freed points or concurrent freed lines create "holes"
  (a freed line in G_i has no jump), which hub-graph edges z_i ~ z'_j could patch (the route p_i -> z_i -> z'_j ->
  (l_j, h) -> points of l_j covers the hole; dually) - not exploited yet.
- 4,804 (1 freed pair) and 4,820 (5 flags) are verified: hubs/graphs/*.sol, hubs/checks/*.

## Pipeline (all tools in research/squads/d10D5/hubs/; COPY them into your card folder and build there)

    cp ../../hubs/*.c ../../hubs/*.py .                      # from research/squads/d10D5/r1/<card>/
    gcc -O2 -o gqgen ../../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 7          # -> gq/gq_q7.bin
    gcc -O3 -march=native -o dmhub dmhub.c -lm && gcc -O3 -march=native -o dmfast_hub dmfast_hub.c -lm
    gcc -O3 -o apsp ../../../../lifts/coordinator_check/apsp.c
    SOL0=../../../../d10D7/graphs/d10D5_n4800_gqdm_q7.sol
    # 1. flags + sigma by perfect matching (prints FLAGS ...; writes k.sol and k.sol.free only if run to the end)
    KMAX=6 python3 flaggreedy.py gq/gq_q7.bin SEED 300 $SOL0 k.sol
    # 2. coset-0 annealing (nu flips + structure-preserving sigma swaps); 0 = done (a few minutes)
    FREE="$(cat k.sol.free)" IN=k.sol OUT=k2.sol BASE=gq/gq_q7.bin NPOLY=4 ITERS=20000000 TEMP0=0.4 TEMP1=0.02 \
        SWAPP=0.002 SEED=1 timeout 900 nice -n 10 ./dmfast_hub 7
    # 3. build hubs + hub graph, exact cost by BFS (0 = diameter 5); ITERS>0 anneals sigma/nu further
    FREE="$(cat k.sol.free)" ITERS=0 ./dmhub gq/gq_q7.bin k2.sol out       # writes out.sol, out.edges
    ./apsp out.edges 10 5                                                    # SCORER: RESULT VALID d=10 D=5 n=...

dmhub env: FREE, H (hubs per side, default 2), ITERS, T0, T1, PNU, PTARG, FOCUS, SEED, COVIT (fast coverage-only
pre-phase), DIAG=1 (list bad pairs), NOHUBG=1 (no hub graph). Its cost counts pairs (source (v,0) or hub, target)
at distance > 5, exactly.

## Rules for every card

- THREADS=1; `timeout 900 nice -n 10` on anything heavy; at most ONE heavy process at a time; <= 1.5 GB memory.
- No git commits. No edits outside your card folder research/squads/d10D5/r1/<card>/ (copy tools in).
- Append ONE line of JSON to research/squads/d10D5/r1/scoreboard.jsonl:
  {"card": "cN", "idea": "<one line>", "code": "<path>", "command": "<exact>", "score": <n of your best VALID graph, or
  the best k / deficiency you reached>, "valid": true|false, "next": "<one line>"}
- Keep any valid graph's .sol and .edges in your folder. Reply in at most 5 lines.
