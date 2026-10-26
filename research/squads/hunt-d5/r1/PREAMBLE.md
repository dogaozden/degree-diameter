# hunt-d5 squad, round 1: shared preamble (read this, then your card)

Problem: bipartite graphs of maximum degree Δ and diameter ≤ 5, as many vertices as possible, in three cells:
(Δ, D) = (5,5), (7,5), (9,5). Our current records: 354, 1,152, 2,662 vertices. Each card names a search window; stay in
it (smaller sizes are already known and do not help).

Key fact (use it): a connected bipartite graph has diameter ≤ 5 iff every two vertices **on the same side** are at
distance ≤ 4. For a Haar graph H(G,S) (vertices (g,A),(g,B), edges (g,A)~(s g,B), s ∈ S, |S| = Δ) this is
(S⁻¹S)² = G and (SS⁻¹)² = G. Counting walks: one side has at most 1 + Δ(Δ−1) + Δ(Δ−1)³ vertices (341 / 1,555 / 4,681).

## Tools (all in research/squads/hunt-d5/tools/, already compiled; run from your card folder with relative paths)

- `python3 ../../tools/gapgroup.py list N` — every group of order N (GAP SmallGroups): "N i abelian |G'| |Z(G)| structure".
- `python3 ../../tools/gapgroup.py table N I OUT.bin [K]` — multiplication table of SmallGroup(N,I) (identity = 0); with K
  also OUT.bin.autK: automorphisms of order K, one per Aut-class, each line "nfix image_0 ... image_{N−1}", fewest fixed
  points first. Tables are big (N² × 2 bytes): keep them in your folder, never commit them (.gitignore covers *.bin).
  Shared tables already made: ../../tables/ (reuse if present).
- `../../tools/haar5 anneal TABLE.bin d SECONDS SEED [OUT]` — annealing for Haar graphs of diameter ≤ 5, cost =
  uncovered elements of (S⁻¹S)² plus of (SS⁻¹)²; prints `RESULT ... best=<cost> ... S= <indices>`. Orbit-symmetric S:
  `AUT=TABLE.bin.aut3 ALINE=0 ORBIT="3 3 0"` (S = m orbits of size k of the automorphism, plus f fixed elements; f
  counts the identity; k·m + f = d). Env K (candidates per move, 16), COOL, REHEAT, RESTART=1.
  `OMP_NUM_THREADS=1 haar5 exh TABLE.bin d [LIMIT]` — exhaustive over S ∋ e for d ≤ 6 (Δ = 5: about a minute per group
  of order 200); prints the exact minimum cost. `haar5 eval TABLE.bin d < sets` — cost of given sets (one per line).
- `../../tools/flift BASE GROUP d 5 SECONDS SEED [K] [OUT]` — voltage-lift annealer: BASE = a small bipartite multigraph
  (text: "b m" then m lines "u v"; base vertices 0..b−1; parallel edges allowed, no loops), GROUP = a table .bin or
  `meta:m:k:r` (Z_m ⋊_r Z_k; `meta:m:1:1` is Z_m). Cost = lift vertices at distance > 5 from the roots. With OUT, writes
  OUT (voltages) and OUT.edges (lift edge list). ~500k evaluations/s.
- `../../tools/lift` — the same over any base size (slower; base up to 8,192 vertices).
- Checker (the scorer for anything you claim): `python3 ../../tools/haar_edges.py TABLE.bin "s0 s1 ..." X.edges` (Haar
  graphs), then `../../tools/apsp X.edges d 5` → must print `RESULT VALID d=<Δ> D=5 n=<vertices>`. flift's OUT.edges goes
  straight into apsp.

## Machine rules (4 cores are shared by 16 cards and the director)

- Single-threaded only (OMP_NUM_THREADS=1, THREADS=1). Every run as `timeout <s> nice -n 10 <cmd>`.
- Budget: about **12 CPU-minutes** for the whole card and **35 minutes wall clock**. Short runs on many candidates beat one
  long run (earlier D = 5 work: plateaus form in under a minute; many short seeds beat a few long runs).
- At most 1.5 GB of memory. No git commands at all (the director commits). Write only inside your card folder.

## What is already known (do not redo)

- Records: (5,5) 354 = Z₅₉-lift of K₃,₃ with two doubled matchings; Haar 352 (a group of order 176). (7,5) 1,152 = Haar
  graph of S₄ × Z₂₄. (9,5) 2,662 = Haar graph of the Heisenberg group mod 11 (order 1,331); 2,640 = SL(2,11) (orbit
  search ORBIT="3 3 0" solves it in 0.5 s, plain annealing stalls at 2).
- Ruled out or weak: lifts of a generalized quadrangle plus one matching (W(3) over Z₄: cost 360; W(5) over Z₄: cost
  6,740); inverse-closed S; abelian groups; plain annealing of general graphs; Cayley-type symmetric S with many fixed
  points; metacyclic Haar groups at Δ = 9 near order 1,378 (1–2 uncovered); AGL(1,25) at Δ = 7 (2 uncovered).
- Near misses are common at cost 1–4; only cost 0 counts.

## Output (this is all the director reads)

Append ONE line of JSON to `research/squads/hunt-d5/r1/scoreboard.jsonl` when you finish:
`{"card": "<id>", "idea": "<one line>", "code": "<path>", "command": "<exact command of the best run>", "score": <vertices
of the best VALID graph, or 0>, "best_cost": <lowest cost reached at the largest size you tried>, "at": "<group/base/size
of that best cost>", "valid": true|false, "next": "<one line>"}`.
Then reply in at most 5 lines. If you find a cost-0 solution, run the apsp check, save the solution (S or voltages) and
the apsp output in your folder, and say so in the first line of your reply.
