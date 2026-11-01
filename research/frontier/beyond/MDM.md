# Multi-doubled-matching lifts of W(q) (diameter 5)

Job new-cells-beyond (Opus director, 2026-10-26). An extension of research/d10D7/DM_D5.md (one doubled matching, Z6) to
k doubled matchings over Z2 × Z(2k+1). It gives (18,5) ≥ 47,600 and (20,5) ≥ 66,640, both from one parity labelling of
W(13), both checked all-pairs.

## Construction

B = incidence graph of W(q) (points P, lines L, |P| = |L| = (q+1)(q²+1), (q+1)-regular, diameter 4).
ν: flags → Z2. σ_1, …, σ_k: bijections P → L (arbitrary). M = 2k+1. The lift has vertices (v, a, b) ∈ V(B) × Z2 × Z_M and
edges, for every point p and every a, b:

- flag (p, l): (p, a, b) ~ (l, a + ν(p,l), b);
- doubled matching i = 1..k, copy c ∈ {0, 1}: (p, a, b) ~ (σ_i(p), a + c, b + i).

It is bipartite, (q+1+2k)-regular and simple (flags keep the Z_M coordinate, σ_i moves it by i ≠ 0, the two copies
differ in Z2), with 2M·2|P| = 4(2k+1)(q+1)(q²+1) vertices.

**Condition (A).** For every pair of opposite points (distance 4 in B) and every pair of opposite lines, the q+1
geodesics joining them do not all have the same ν-parity.

## Theorem

If ν satisfies (A), the lift has diameter ≤ 5 for every k ≥ 1 and every choice of σ_1, …, σ_k.

*Proof.* Take x = (v, a, b), y = (u, a', b'), δ = b' − b ∈ Z_M, ε = a' − a. A walk in B lifts to a walk from x with the
same length; its Z2-coordinate changes by the ν-parity of its flags plus the copies used on matching edges, its Z_M
coordinate by the signed sum of the matching indices used (point → line +i, line → point −i). In B, two vertices of
opposite colour are at distance ≤ 3 and two of the same colour at distance ≤ 4. Each geodesic of length ≤ 3 is unique.

1. δ = +i, i ∈ {1..k}, v and u points: x → (σ_i(v), a + c, b + i), then the lifted geodesic σ_i(v) → u (length ≤ 3,
   parity π). Choosing c = ε − π reaches y in ≤ 4 steps. δ = −i: the lifted geodesic v → σ_i(u) (≤ 3, parity π), then
   the back jump σ_i(u) → u on the copy c with π + c = ε: ≤ 4 steps.
   Lines are the same with σ_i⁻¹.
2. δ = ±i, v a point, u a line: +i: jump v → σ_i(v), then the geodesic between the lines σ_i(v) and u (≤ 4): ≤ 5. −i:
   take a point p on u; geodesic v → σ_i(p) (≤ 3), back jump to p, step p → u: ≤ 5. The copy fixes the parity.
   (v a line, u a point: reverse a path of the previous kind.)
3. δ = 0, same colour, d_B(v,u) ≤ 2 (also v = u): the lifted geodesic gives one parity in ≤ 2 steps; appending the
   2-cycle v → σ_1(v) → v that goes out on one copy and back on the other flips the parity and keeps b: ≤ 4 steps.
4. δ = 0, same colour, d_B(v,u) = 4: by (A) two of the q+1 geodesics have different parities: both parities in 4 steps.
5. δ = 0, opposite colours: the geodesic (≤ 3), or the geodesic plus the 2-cycle of case 3 (≤ 5).

So every pair is within 5 (same-colour pairs within 4). ∎

The cases are those of DM_D5.md's proof for k = 1; the only new point is that {0, ±1, …, ±k} = Z_M, so one jump reaches
every non-zero Z_M class, and the two copies of each matching supply both Z2 classes. Condition (A) is DM_D5's condition
without its "routes"; dmfast (research/d10D7/dmfast.c) with NOROUTE=1 anneals exactly (A).

## Instances

| cell | q | k | vertices | ν | check |
|---|---|---|---|---|---|
| (18,5) | 13 | 2 | **47,600** | mdm/nu_q13_s2.txt (dmfast seed 2, 16,837 flips, 8 s) | apsp VALID, diameter 5, 18-regular |
| (20,5) | 13 | 3 | **66,640** | same ν | apsp VALID, diameter 5, 20-regular |
| (19,5) | 16 | 1 | **52,428** | DM_D5's k = 1 case; ν, σ from squad r1/c05 (dmfast with routes) | apsp VALID |
| (13,5) | 8 | 2 | **11,700** | squad r2/d05: ν, σ_1, σ_2 annealed with a route-aware cost (mdm8.c) | apsp VALID + bfs_all (all pairs); old record 11,486 |

Random ν fails (A) on a fraction 2^−q of the opposite pairs (641 of 5,228,860 at q = 13), against about q⁴ free
parities, so (A) is easy for q ≥ 9 or so. At q = 8 (W(8), k = 2 would give (13,5) ≥ 11,700 against our 11,486) the
anneal is tighter: see the log in this folder.

Rebuild: `cd research/frontier/beyond/mdm && gcc -O3 -o gqgen ../../../d10D7/gqgen.c && mkdir -p gq && ./gqgen 13 &&
python3 build_mdm.py gq/gq_q13.bin nu_q13_s2.txt K 1 OUT.edges` (K = 2 or 3; σ_1 from the ν file, σ_2, σ_3 from the
seed), then `apsp OUT.edges 14+2K 5`.

Family values (Δ = q+1+2k, 4(2k+1)(q+1)(q²+1)): with q = 13 the same ν gives (16,5) 28,560, (18,5) 47,600, (20,5) 66,640.
In the old table range it beats a record only at (13,5): q = 8, k = 2 gives 11,700 > 11,486 (lab) > 11,480 (2013 table).
On W(8) pure (A) stalls near 20 failing pairs (director's dmfast runs), but routes through the matchings (walks of
length ≤ 4 with jump sum ≡ 0 mod 5 and at least one jump reach both Z2 classes of coset 0) cover them: squad card r2/d05
annealed ν, σ_1 and σ_2 together against that cost and reached 0 far pairs in about two minutes. The graph is 13-regular
with diameter exactly 5 (graphs/d13D5_n11700_W8_2dm_Z10.edges.gz; checks/d13D5_n11700_W8_2dm_Z10.check.txt; rebuilt
identically from research/squads/beyond/r2/d05/st_run2.txt).

## Referee (squad card r2/d06)

The card re-read the proof case by case and found no gap (both colours, all distance types, simplicity, regularity).
Computer tests: with the director's ν on W(13), k = 1 gives 28,560 vertices with diameter 5 (apsp VALID); a ν with
exactly one opposite pair failing (A) (built by a targeted dmfast run) gives diameter 6, as the proof predicts when no
route rescues the pair. Pure (A) was not reached by annealing at q = 3, 4, 5, 7 (best 17, 11, 65, 48 failing pairs), in
line with the first-moment count; at q = 4, k = 3 the best ν still gives diameter 5 through routes (2,380 vertices),
so (A) is sufficient, not necessary. Files: research/squads/beyond/r2/d06/.
