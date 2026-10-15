# The "+2" graphs: a fourth hat

Research by the `plus2-opus` agent (Claude Opus), 2026-10-10. Checked by the main session (see the end).

## Short version
- All three found graphs (192, 276, 376) do the same thing. Araujo-Pardo and López (AL) add three "hat" pairs to PG(2,q). The search added a **fourth hat pair**.
- A hat pair is two new vertices: a copy of a point on a special line ℓ, and a copy of a line through a special point A.
- To make room, a few old incidences in a small "gadget" near ℓ and A had to change. The search found a different gadget fix for each q.
- The clean version of the fix is a 3-cycle "rotation" of three incidences. It works in **every projective plane of order q ≥ 4**. It gives a bipartite graph with 2(q²+q+6) vertices, maximum degree q+2 and diameter 3, which is AL + 2. A proof is in section 4; computer checks agree.
- **No new table entry.** In the table range this only matters for Δ = 7, 11, 13, 15. We already hold 11, 13 and 15. For Δ = 7 the rule gives 72, but the table has 80.
- **Going further:** a SAT solver says +3 and +4 are impossible inside the hat family (q = 5…13). A local search did not grow the +2 graph for q = 7 or 9. It did grow q = 5 from 72 to 74, which does not matter because (7,3) is already at 80.

## 1. What the +2 did
Coordinates as in AL: points (x,y), P_m, P; lines [m,b] (y = mx+b), L_c (x = c), L. Everything happens around two objects:
- the line **ℓ = L_0** (x = 0), with points P and (0,y);
- the point **A = P_0** (horizontal direction), with lines L and [0,b]. A is not on ℓ, and (0,y) lies on [0,y].

A **hat pair at row s** is:
- Ĥ_s, a copy of the point (0,s). It lies on every line through (0,s) except ℓ, which are the q lines [m,s].
- K̂_s, a copy of the line [0,s]. It holds every point of [0,s] except A, which are the q points (t,s).

AL use hats at rows S = {0,1,a}, plus Q0 (a copy of A) and M0 (a copy of ℓ). That is 8 new vertices. AL's final "matching" is only filler: delete it and the diameter is still 3 (core_check.py).

**The AL graph is not an induced subgraph, and cannot be.** AL is (q+2)-regular, so its vertices have no free degree for edges to the new vertices. Any +2 graph must therefore delete AL edges. Comparing labels directly (the programs keep AL's labels), the found graphs delete 60, 94 and 136 AL edges. Most of that is the annealer reshuffling filler.

**The two new vertices form a fourth hat pair at a new row c:**

| q | c | new point lies on | new line holds |
|---|---|---|---|
| 9 | 8 | all [m,8]; M0; K̂_1 | all (t,8); Q0; Ĥ_0 |
| 11 | 4 | all [m,4]; ℓ; [0,0] | all (t,4); A; (0,1) |
| 13 | 3 | all [m,3]; M0; ℓ | all (t,3); Q0; A |

(Field elements are lib.GF integer codes.)

**Where the degree came from:**
- The lines [m,c] and points (t,c) each give up their AL filler edge (t,c)–[t,c].
- Every other change is inside the gadget: the points {A, P, (0,y), Q0, hats} against the lines {ℓ, L, [0,y], M0, hat lines}. The plane incidences removed are:
  - q=9: (0,0)∉[0,0], (0,1)∉[0,1], (0,8)∉[0,8], plus AL's (0,a)∉[0,a]. In their place: (0,1)∈[0,0], (0,8)∈[0,1], (0,0)∈[0,8]. This is a 3-cycle.
  - q=11: (0,0)∉[0,0], (0,1)∉[0,1], (0,2)∉[0,2], (0,4)∉[0,4], (0,4)∉ℓ, A∉[0,4]. Needed non-plane edge: (0,0)∈[0,1].
  - q=13: (0,0)∉[0,0], (0,1)∉[0,1], (0,2)∉[0,2], (0,3)∉[0,3], (0,2)∉ℓ, A∉[0,2]. Needed non-plane edge: (0,1)∈[0,0].
- found_vs_rule.py checks this. Outside the gadget, each found graph is exactly "PG(2,q) + four hats" plus filler (48, 80 and 120 filler edges). Nothing outside the gadget is missing or extra.

## 2. Is it one rule?
The skeleton is the same in all three: a fourth hat pair. The gadget fix is not.
- The q=9 graph is exactly the clean rule below, up to filler.
- At q=11, Ĥ_4 takes (0,4)'s place on ℓ, and K̂_4 takes [0,4]'s place at A.
- At q=13 the same kind of swap happens at row a=2.
So the search found one idea and three ways to finish it.

## 3. The construction (construction.py, coordinate-free)
Take a projective plane Π of order q ≥ 4. Choose:
- a line ℓ, and a point A not on ℓ;
- a point P on ℓ, and let m = AP;
- four distinct points X0, X1, Xa, Xc on ℓ, none equal to P.

Write AX for the line through A and X. Let ℓ* = ℓ \ {X0, X1, Xc}. It has q−2 points, including P and Xa.

New points: Q, H0, H1, Ha, Hc. New lines: M, K0, K1, Ka, Kc. The incidences are:
1. All incidences of Π, minus (Xs, AXs) for s = 0, 1, a, c. Then add the **rotation**: X1 on AX0, Xc on AX1, X0 on AXc.
2. Hs lies on every line of Π through Xs except ℓ.
3. Ks holds every point of Π on AXs except A.
4. M holds ℓ* and H0, H1, Ha, Hc.
5. Q lies on AX for each X in ℓ* (this includes m), and on K0, K1, Ka, Kc.
6. A on Ka; Ha on ℓ; H0 on Kc; Hc on K1; H1 on K0.

Optionally add a maximum matching as filler. In every case tested, this makes the graph regular.

The dictionary to AL's coordinates is ℓ = L_0, A = P_0, Xs = (0,s), AXs = [0,s]. AL itself is this scheme with three hats, no rotation, and H0~K1, H1~K0.

Results (all pass scripts/verify_record.py; all (q+2)-regular; saved as graphs/plus2_q{q}_d{q+2}_n{n}.json):

| q | Δ | AL | this rule | Moore | wiki (Δ,3) |
|---|---|---|---|---|---|
| 2, 3 | 4, 5 | – | needs q≥4 | 30, 42 | Moore |
| 4 | 6 | 50 | 52 | 62 | 62 Moore |
| 5 | 7 | 70 | 72 | 86 | **80** |
| 7 | 9 | 122 | 124 | 146 | 146 Moore |
| 8 | 10 | 154 | 156 | 182 | 182 Moore |
| 9 | 11 | 190 | 192 | 222 | 190 (ours already) |
| 11 | 13 | 274 | 276 | 314 | 274 (ours already) |
| 13 | 15 | 374 | 376 | 422 | 374 (ours already) |
| 16 | 18 | 554 | 556 | 614 | not tabled (Moore exists) |

Robustness checks, all valid:
- every ordered choice of (X0,X1,Xa,Xc) for q = 4, 5, 7, 8, 9 (check_all.out). PGL(3,q) is transitive on the (A,ℓ,P) choices, so this is every input in PG(2,q) for these q;
- 300 random choices each for q = 11 and 13;
- 200 random frames in each of two nearfield planes of order 9 (nearfield_plane.py). These planes are not Desarguesian.

**No new table beat.** The rule only matters where q+1 is not a prime power (where it is, a bipartite Moore graph exists). Beyond the table it gives AL+2 for Δ = 21, 25, 27, 29, …

## 4. Proof
**Theorem.** For any projective plane of order q ≥ 4 and any choices as above, the incidence graph G of the structure 𝒮 (without filler) is bipartite, has 2(q²+q+6) vertices, maximum degree q+2 and diameter 3.

**Step 0 (reduction).** Suppose every two points share a line and every two lines share a point. Then the diameter is at most 3. For a point p not on a line L, take any point p′ on L and a line L′ through p and p′; this gives the path p–L′–p′–L.

**Step 1 (degrees).** Each count below is: plane degree − removed + added.
- Points not on ℓ and not A gain at most Ks, since a point other than A lies on exactly one line through A. So they have degree ≤ q+2.
- A: +Ka.
- P and X ∈ ℓ* \ {Xa}: +M.
- Xa: −AXa +M +Ka.
- X0: −AX0 +AXc +K0. X1: −AX1 +AX0 +K1. Xc: −AXc +AX1 +Kc.
- Q: (q−2) + 4.
- Hs: q + M + one more. The one more is ℓ, Kc, K1 or K0.
- Lines of Π not through A and not ℓ lose nothing, and gain at most one hat point, since they meet ℓ once.
- ℓ: +Ha. m and AX for X ∈ ℓ* \ {Xa}: +Q.
- AXa: −Xa +Q +Ha. AX0: −X0 +X1 +H0. AX1: −X1 +Xc +H1. AXc: −Xc +X0 +Hc.
- M: (q−2) + 4. Ks: q + Q + one more (A, H1, Hc or H0).
Every degree is ≤ q+2. Π has q²+q+1 points and we add 5 new ones, so the order is 2(q²+q+6).

**Step 2 (any two points are collinear).** Only the four incidences (Xs, AXs) were removed.
- (a) Two plane points u, v. Let L = uv. If both incidences survive, done. Otherwise L = AXs and u = Xs.
  - If v ≠ A, both are on Ks.
  - If v = A: for s=a use Ka; for s=0 use AXc; for s=1 use AX0; for s=c use AX1.
- (b) Q and a plane point u.
  - u = A: use m.
  - u ∈ ℓ* \ {Xa}: use Au. u = Xa: use Ka.
  - u = Xs with s ∈ {0,1,c}: use Ks.
  - u off ℓ, with Au ∩ ℓ = X. If X ∈ ℓ*, use AX. Otherwise X = Xs and u ∈ Ks.
- (c) Hs and a plane point u.
  - u off ℓ (this includes A): use the line uXs, which is not ℓ.
  - u = Xs: use any line through Xs other than ℓ and AXs.
  - u ∈ ℓ*: use M.
  - u ∈ {X0, X1, Xc}, u ≠ Xs:
    - s=a: use ℓ.
    - s=0: X1 via AX0 (rotation); Xc via Kc.
    - s=1: Xc via AX1; X0 via K0.
    - s=c: X0 via AXc; X1 via K1.
- (d) Two new points.
  - Hs and Ht: use M.
  - Q with H0: Kc. Q with Hc: K1. Q with H1: K0. Q with Ha: AXa.

**Step 3 (any two lines meet), by duality.** Run the same construction in the dual plane. Use the anti-flag (ℓ, A), the point m on the line A, and X0′=AX0, X1′=AXc, Xa′=AXa, Xc′=AX1 (note that 1 and c swap). Items 1–6 then return exactly 𝒮 with points and lines exchanged:
- H0′=K0, H1′=Kc, Ha′=Ka, Hc′=K1;
- K0′=H0, K1′=Hc, Ka′=Ha, Kc′=H1;
- Q′=M, M′=Q.
For example, "X1′ on A′X0′" reads "X0 on AXc". So Step 2 in the dual plane proves Step 3. ∎

The proof uses only the plane axioms, plus q ≥ 4 so that ℓ has four points besides P. It therefore holds for all prime powers q ≥ 4, including non-Desarguesian planes.

## 5. Going further (computer evidence only)
**Heuristic: why four hats and not five.** Hs already sees every point off ℓ. It still has to see the other q points of ℓ, the other hats and Q, using only 2 spare incidences. Old lines other than ℓ contain only one point of ℓ. So those 2 incidences must go to:
- ℓ itself (one spare slot, so one hat only);
- M (q+2 slots, which it shares with the hats);
- a K-line;
- or the hat's own rotated line AXs (one extra point of ℓ).
With 3 hats, M misses 2 points of ℓ. With 4 hats, M misses 3, and each hat needs 2 of them; the rotation supplies the second. With 5 hats, M misses 4 and each hat would need 3.
Hats must also sit on one line through one point: two hat points at X and Y would both add themselves to the line XY. So a "second application of the rule" is really just a fifth hat in the same gadget.

**SAT inside the hat family** (sat_gadget.py; CaDiCaL via python-sat in a scratch venv, not in the repo venv). The bulk is fixed and every gadget incidence is free. Constraints: degree ≤ q+2, every two points collinear, every two lines concurrent.
- Positive controls: AL (3,3,1,1) and +2 (4,4,1,1) are SAT, and the solutions are valid graphs.
- Columns below are (hat points, hat lines, Q's, M's). Each UNSAT took under 2 s.
  - +3 (5,4,1,1): UNSAT for q = 5, 7, 9, 11, 13.
  - +3 (4,4,2,1): UNSAT for q = 5, 7, 9, 11, 13.
  - +3 (6,4,0,1): UNSAT for q = 5, 7.
  - +4 (5,5,1,1), (4,4,2,2), (6,6,0,0) and (6,5,0,1): UNSAT for q = 5, 7, 9, 11, 13.
  - +4 (5,5,2,0), (3,3,3,3) and (5,4,2,1): UNSAT for q = 5, 7.
- Caveat: the hats sit at fixed points of ℓ and the bulk is fixed. This rules out the hat family only, not other graphs.
- Re-run 2026-10-15 for the website's step-through, which offers q = 4, 5, 7, 8, 9, 11 and 13. The model is unchanged; the runs are not saved in the repo.
  - A fifth hat, (5,5,1,1), is also UNSAT at q = 4 and q = 8 in the default frame. The AL and +2 controls are SAT there, and their decoded graphs are valid.
  - It is also UNSAT in random frames 1, 2 and 3 at q = 5 and q = 8, with the +2 control SAT and valid in each.

**Looser SAT** (sat_free.py). The new vertices have all incidences free, and so do the plane incidences inside the gadget. It finds AL and +2 for q = 4 and 5. For +3 it did not finish: (6,5) at q=4 ran 150 s and at q=5 ran 500 s, both unresolved. That model has no symmetry breaking.

**Local search** (grow_from_plus2.py). The 376 program's C engine was given the +2 graph and asked to grow by 2.
- q=5: one of two 300 s runs reached 74 (graphs/grown_q5_n74_seed2.json; 7-regular; passes verify_record). This is below the (7,3) record of 80. It is unstructured annealer output, and small q has a lot of slack.
- q=7: two 420 s runs, no growth.
- q=9: one 300 s run and one 420 s run, no growth.
This matches the islands, which never found 194.

## Files
- construction.py, save_graphs.py, graphs/plus2_*.json, check_all.py (+ check_all.out), nearfield_plane.py
- al.py, plus2.py (named versions in AL's coordinates)
- Analysis of the found graphs: diff_al.py, inspect_diff.py, found_core.py, found_detail.py, found_vs_rule.py, core_check.py
- sat_gadget.py and sat_free.py (+ satfree_q5_65.out), plus graphs/sat_*.json (SAT controls)
- grow_from_plus2.py (+ grow_*.out), graphs/grown_q5_n74_seed2.json

## Checked by the main session (2026-10-10)
- I rebuilt the construction from the six rules in section 3 alone, without using the agent's code (`indep_check.py` here). It gives valid graphs (degree ≤ q+2, diameter 3, order 2(q²+q+6)) for every random frame tried: 30 frames each for q = 4, 5, 7, 8, 9; 8 each for q = 11, 13; 3 for q = 16.
- The rebuilt graphs for q = 4, 5, 7, 8, 9, 11, 13 and 16 pass all three checkers in `scripts/verify_record.py`.
- Negative controls fail as they should: dropping the rotation, or dropping the link H1–K0, gives diameter above 3 for q = 5, 9 and 13.
- I read the proof and found no gap. It is a proof written by a model and checked here by computer on PG(2,q) for q up to 16; it still needs a reading by a mathematician before it goes in a paper.
- **Lean (2026-10-11):** the theorem is formalized in `lean/BipartiteDD/Plus2/` (`plus2`, `plus2_of_order`), with only the three standard axioms. This replaces the need to trust the prose proof, provided the definitions in `Plus2/Defs.lean` match section 3; they were written to it rule by rule.
