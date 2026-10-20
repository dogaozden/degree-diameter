# Problem 4, diameter 4 (p4-d4-opus) — interim, saved by the main session from the agent's message (23:35)

1. NOTE.md open problem 3 is answered NO: q²+1 line copies with stand-ins cannot exist for odd q. Dual form: M = point
   set of W(3,q), at most 1 point on each totally isotropic line outside the spread S, at most 2 on each S-line. Double
   counting over points outside M forces no S-line to hold 2 points, so M would be an ovoid of W(3,q), which does not
   exist for odd q. The same argument covers the j ≥ 3 relaxation only for 0/1 sets. (Correction, ~00:20: weighted 3-covers of Q(4,q) exist for q = 3, 5, 7, so at odd j ≥ 3 the gap closes: n_b(q+1+j,4) ≥ 2(q²+1)(q+1+j) for those q.)
2. Exact optima (CP-SAT): q=3: 8; q=5: 21 (matches the old ILP). q=7: ≥ 40 by tabu and Singer-subgroup ILP, so
   890 > AS(7) = 882. That cell is a Moore cell (GQ exists), so it is only evidence.
3. q=9 is the live case: |M| ≥ 61 is needed to beat 1782. The antipodal-pair subfamily gives only 50 so far. General
   tabu search running.
4. Δ = 6, 8, 9, 10, 12, 14 are Moore cells at D = 4 (GQ(Δ−1,Δ−1) exists), so the table is optimal there. In table
   range the only open D = 4 cells are 7, 11, 13, 15, 16. Next: tabulate Δ > 16 against our own constructions.
Code: research/p4/d4 (w3k.py, cp_m.py, pq.py, hs.c, groups.py).

## Update ~00:20 (from the agent's messages)
- Upper bound, proved: with stand-ins, |M| ≤ q²−q+2 for odd q. If a spread line holds 2 points of M, its q−1 other
  points each see at most q points of M, and together they see all of M except those 2. If no spread line holds 2,
  Tallini's q²−q+1 applies.
- Weighted 3-ovoids of W(3,q) exist for q = 3, 5, 7 (CP-SAT; q = 5 even has a 0/1 3-ovoid). They are weighted 3-covers
  of Q(4,q), so Cor. B1 gives n_b(q+4,4) ≥ 2(q²+1)(q+4) with no stand-ins; with 2-ovoids added, for every odd j ≥ 3.
  If this holds for all odd q, B2's odd case improves from 2q²Δ to 2(q²+1)Δ for Δ ≥ q+4 (first such cell Δ = 41;
  no table cell ≤ 16 affected).
- q = 9 stand-in best 56 (needs 61 to beat 1782). q = 11, 13 runs started. Cloud: C (weighted 3-ovoids, branch
  p4-d4-3) session_01FXg91CE77JRUHqDm5hMWFJ; A and B launching.
- Theorem B dual builder works end to end: graphs/q4st_q7_n890.json passes verify_record (9,4) (a Moore cell; pipeline
  check only).

## Update 00:30 (from the agent's message)
- Clouds: A q=9 search (session_0132DUXSq8VcQPWVgCi9mAvv, branch p4-d4-1); B q=11/13 (session_011DG3j5iMDDmLx41CKtfTSX,
  p4-d4-2); C weighted 3-ovoids (session_01FXg91CE77JRUHqDm5hMWFJ, p4-d4-3).
- Best stand-in sets M (W(3,q) points, ≤ 1 per t.i. line outside S, ≤ 2 per S-line; order
  2(q+1)(q²+1) + (q²+1) + |M|; upper bound q²−q+2):
  q=7: 40 (needs 33 to beat AS); graphs/q4st_q7_n890.json verified (Moore cell).
  q=9: 56 (needs 61) → 1778 < 1782. Same 56 from tabu and CP-SAT with a symmetry of order 4; Kantor–Knuth spread gives 55.
  q=11: 76 so far (needs 97). q=13: 90 so far (needs 141).
  |M|/q² drops with q (0.82, 0.69, 0.63, …); expectation: stand-ins will not beat Theorem A at Δ = 11/13/15.
- The q=7 optimum is structured: antipodal pairs on 20 spread lines; in the Singer model the pair indices are
  {0,13,29,32}+40k mod 200, invariant under the order-10 Singer subgroup. The analogous subgroups do not exist for q = 9,
  11 ((q²+1)/2 = 41 and 61 are prime), which may explain the drop.
- Correction: the first Δ where weighted 3-ovoids of W(3,q) would matter is Δ = 23 (q = 19, j = 3; +46 over AS(19)), then
  41, 47, 53, 57, 59 below 64. Full D = 4 table for Δ ≤ 64: research/p4/d4/dtable.py (python3 dtable.py 5 64).
- Weighted 3-ovoids with F-torus symmetry: found at q = 7; ruled out for q = 9, 11, 13 under that symmetry; unsymmetric
  search in cloud C.

## Update ~01:15: regular versions (AL20 Problem 4 asks for regular graphs)
Every Cor. B1 graph can be made Δ-regular. Originals already have degree Δ. The point copies (Σw = (Δ−s−1)(st+1), each of
degree t+1) and the line copies (|M| = (Δ−t−1)(st+1), each of degree s+1) sit on opposite sides and miss exactly the
same total degree, so add a biregular bipartite graph between them (degrees Δ−t−1 and Δ−s−1; cyclic matchings work).
Adding edges cannot increase distances; two non-collinear original points still have no common neighbour, so the
diameter stays exactly 4.
Consequence: for every prime power q and Δ ≥ q+1 there is a Δ-regular bipartite graph of diameter 4 and order
2Δ(q²+1) when q is even or Δ−q−1 is even (Q(4,q)), else 2Δq² (AS(q), Theorem A copies plus fibre-spread copies).
Verified: graphs/regular_c1_q13_n5440.json is 16-regular, passes verify_record (16,4): 5440 vertices, sides 2720+2720,
43520 edges (build_regular.py). 1782/3146/5070 were regular already. Also graphs/w3cover_q7_n1100.json (weighted
3-cover of Q(4,7)) passes (11,4) — pipeline check only.
