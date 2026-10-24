# Δ = q+2, D = 7 from the generalized hexagon H(q): the table construction plus hub vertices

exp2-squad (Opus), 2026-10-24. Code: `d7hex.c` (this folder). H(q) from `research/p4/d6/hexgen.c` (split Cayley
hexagon, q = p or p²). Checks: `research/lifts/coordinator_check/apsp.c` (all-pairs, bit-parallel BFS).

## 1. The table values at D = 7 are 3·|H(q)|

The three target cells decode exactly: (7,7) = 23,436 = 3·7,812 = 3·|H(5)|, (9,7) = 117,648 = 3·|H(7)|,
(11,7) = 398,580 = 3·|H(9)|, with Δ = q+2. (Also (10,7) = 3·|H(8)|, (13,7) = 3·|H(11)|, and (12,7), (14,7), (16,7)
are 5·|H(q)| with Δ = q+3.) The wiki credits D = 7, Δ ≥ 6 to Delorme, Gómez and Quisquater.

**Construction X(M).** Let P, L be the points and lines of H(q) (|P| = |L| = n = (q⁶−1)/(q−1)) and M: P → L any
bijection. Vertices (v, i), v ∈ P ∪ L, i ∈ Z₃. Edges: (p, i) ~ (l, i) when p ∈ l, and (p, i) ~ (M(p), i+1).
Bipartite (points | lines), (q+2)-regular, 6n vertices.

**Lemma.** X(M) has diameter ≤ 7 for every bijection M.
*Proof.* H(q) has diameter 6 and point–line distances ≤ 5. By the Z₃ symmetry take sources at level 0.
From a point (p,0): level 0 by hexagon paths; level 1 by (p,0) → (M(p),1) then a hexagon path (points ≤ 1+5,
lines ≤ 1+6); level −1: a point x by (p,0) ⇝ (M(x),0) → (x,−1), length ≤ 5+1; a line l by the same route to some
x ∈ l and one more step, ≤ 7. From a line (l,0): level −1 by (l,0) → (M⁻¹(l),−1) then a hexagon path (≤ 1+6 to
points, ≤ 1+5 to lines); level +1: a line l' by (l,0) ⇝ (M⁻¹(l'),0) → (l',1), ≤ 5+1; a point x by the same route
to a line through x and one more step, ≤ 7. ∎

So the construction needs no special matching at all, which leaves room to change it locally.

## 2. Hubs: +2 vertices per freed pair

Pick a point p ("freed"), delete its three extra edges (p,i)–(M(p),i+1), and add two new vertices:
a line-side hub z ~ (p,0), (p,1), (p,2) and a point-side hub z' ~ (M(p),0), (M(p),1), (M(p),2). Degrees stay ≤ q+2.

- z and z' reach every vertex within 7 (one step to level i, then a hexagon path), and the two hubs of one pair are
  within 7 of each other.
- Every route in the Lemma survives except those that use a deleted edge as the source's own up-edge (source (p,i)),
  the source's own down-edge (source (M(p),i)), or the target's own edge (targets (p,i) and (M(p),i), which is the
  same condition read backwards). For targets that are lines (resp. points) the Lemma may use any point on the line
  (any line through the point), so a different one is used.
- Hence X stays at diameter 7 iff (p,0) reaches all of level 1 and (M(p),0) reaches all of level −1 within 7. Via
  the hub, (p,0) → z → (p,1) covers level 1 except the points opposite p, and (M(p),0) → z' → (M(p),−1) covers level −1
  except the lines opposite M(p). The opposite ones are covered by routes such as (p,0) ⇝ (u,0) → (M(u),1) → (x,1) with
  u at distance 4 from p and x ∈ M(u), so M is re-chosen near p and near M(p) by a targeted local search.
- **Algebraic cover (one pair, no search).** Take M(p) = l with p on l, S′(p) = {points u : d(p,u) = 4, d(l,u) = 5}
  (q⁴ points, reached from p first through a line ≠ l) and S(l) = {lines N : d(l,N) = 4, d(p,N) = 5} (q⁴ lines). In a
  generalized hexagon every point x opposite p lies on exactly one line of S(l) (the first line of the geodesic from x
  to l), and every line t opposite l contains exactly one point of S′(p) (its point nearest to p). So if M maps S′(p)
  onto S(l), in any order, then (p,0) ~> (u,0) -> (M(u),1) -> (x,1) and (l,0) ~> (M(y),0) -> (y,−1) -> (t,−1) cover
  everything the hubs miss (length ≤ 6). One freed pair needs no search at all.
- With several freed pairs, hubs of the same side must also be within 6 of each other (for points p, p' at distance 6
  they are at distance 8), so freed points must be close or the hubs linked.

## 3. Results (all checked by apsp.c on the written edge list)

| cell | table | ours | construction | check |
|---|---|---|---|---|
| (7,7) | 23,436 | 23,438 | H(5), one freed pair | checks/d7D7_hex5_K1_n23438.apsp.txt |
| (7,7) | 23,436 | 23,462 | H(5), 13 freed pairs, PG(2,3) hub graph | checks/d7D7_hex5_K13pg23_n23462.apsp.txt |
| (7,7) | 23,436 | 23,472 | H(5), 18 freed pairs, random hub graph (squad r1/c2) | checks/d7D7_hex5_K18rnd_n23472.apsp.txt |
| (7,7) | 23,436 | 23,484 | H(5), 24 freed pairs, random hub graph | checks/d7D7_hex5_K24rnd_n23484.apsp.txt |
| (7,7) | 23,436 | **23,488** | H(5), 26 freed pairs, random hub graph | checks/d7D7_hex5_K26rnd_n23488.apsp.txt |
| (9,7) | 117,648 | 117,650 | H(7), one freed pair | checks/d9D7_hex7_K1_n117650.apsp.txt |
| (9,7) | 117,648 | 117,674 | H(7), 13 freed pairs, PG(2,3) hub graph (squad r1/c3) | checks/d9D7_hex7_K13pg23_n117674.apsp.txt |
| (9,7) | 117,648 | **117,690** | H(7), 21 freed pairs, PG(2,4) hub graph | checks/d9D7_hex7_K21pg24_n117690.apsp.txt |
| (11,7) | 398,580 | 398,582 | H(9), one freed pair (algebraic cover, no search) | checks/d11D7_hex9_K1_n398582.apsp.txt |
| (11,7) | 398,580 | **398,606** | H(9), 13 freed pairs, PG(2,3) hub graph | checks/d11D7_hex9_K13pg23_n398606.apsp.txt |

Solution files: `research/frontier/sols/d7D7_hex*.sol`, `d9D7_hex*.sol`, `d11D7_hex*.sol` (format in d7hex.c's
header: q, N, K, n; the freed points; the hub graph edges; then M). These are not Haar graphs, so build_haar2.py does not
apply. Rebuild: `gcc -O2 -o hexgen research/p4/d6/hexgen.c && mkdir -p hex && ./hexgen 5` (writes hex/hex_q5.bin; also
7, 9), `gcc -O2 -o d7hex d7hex.c -lm`, `./d7hex edges hex/hex_q5.bin SOL edges.txt`, then
`apsp edges.txt 7 7` (Δ first; 9 for q = 7, 11 for q = 9).

## 4. Search (d7hex search)

- Freed points pairwise ≥ mind apart; hubs linked by a hub graph (PG(2,q−2) built in, or any file with hub degrees ≤ q−1).
- Each pair gets the algebraic cover (§2) in turn; pairs then conflict where their S′ and S sets overlap.
- Fast search: incremental counts of real routes of length ≤ 6 (type 4: u at distance 4 from p, M(u) through the target;
  type 2: u collinear with p, target within 3 of M(u); the duals for lines; static routes through the hub graph);
  swap moves on M aimed at uncovered targets, best-of-k, simulated annealing; proxy 0 implies every freed source has
  eccentricity ≤ 7 (checked by BFS, then by apsp on the whole graph).
- Type-2 pre-pass (alg 3): routes through the q(q+1) points collinear with p use few points per pair, so pairs rarely
  compete for them; it covers ~77 % of each pair's targets at q = 5 and makes K = 13 solve 4× faster there.
- Pair dropping: DROP=1 drops the worst pairs at the end; DROPSEC/DROPSTART drop pairs during the search when it stalls.
