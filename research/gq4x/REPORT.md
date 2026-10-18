# Diameter 4 from quadrangles: weighted ovoids, covers and stand-ins

gq-expand-opus (Claude Opus), 2026-10-18. Code and graphs are in research/gq4x/.

## Credit

- Copying vertices is from Delorme & Farhi (1984).
- Copying an ovoid-type point set in a GQ incidence graph is from Delorme, Europ. J. Combin. 6 (1985) 291-302, Sec. 7-8(a). That gives exactly the old table values 346, 1734, 3064, 4946 and 5134 (https://web.mat.upc.edu/francesc.comellas/delta-d/papers/81981341.pdf).
- The novelty check found no prior art for three things here:
  - the AS(q) construction with two elliptic quadrics (Theorem A);
  - copies of a line multiset (partial spreads, 2-covers);
  - stand-ins (Theorem B).

## Summary

| cell | construction | order | before | status |
|---|---|---|---|---|
| (11,4) | AS(9) + Theorem A | **1782** | 1774 (ours), table 1734 | verified, committed |
| (13,4) | AS(11) + Theorem A | **3146** | 3122 (ours), table 3064 | verified, committed |
| (15,4) | AS(13) + Theorem A | **5070** | 5022 (ours), table 4946 | verified, committed |
| (16,4) | AS(13) + Theorem A + partial ovoid 86 + spread | 5325 | 5284 | verified; now beaten by 5357 (Q(4,13), partial 2-cover) |

The first three graphs are (q+2)-regular with equal sides. Check files: graphs/verify_as_w2.txt and graphs/verify_as_deg3_q13.txt.

## 1. The quadrangle AS(q) = P(W(q),x)

Setup:
- W(q): points of PG(3,q); lines are the totally isotropic lines of f(u,v) = u0v1 - u1v0 + u2v3 - u3v2.
- Payne's derivation at x = (1,0,0,0) gives a GQ of order (q-1, q+1). For q odd this is the Ahrens-Szekeres quadrangle AS(q) (Payne-Thas, FGQ §3.2.6; cited from memory).

Coordinates:
- G = GF(q) x GF(q)^2, with the product (a,w)(a',w') = (a+a'+det(w,w'), w+w'). Here det((b,c),(b',c')) = bc' - cb'.
- Points are the q^3 elements of G; (a,(b,c)) stands for the vector (a,1,b,c).
- Lines come in two kinds:
  - left cosets of the q+1 subgroups Z_d = {(0,λd)}. Explicitly: {(a0 + λ·det(w0,d), w0+λd) : λ}. These are the isotropic lines through a point of x^⊥ other than x.
  - left cosets of Z = {(μ,0)}, the "fibres" over each w. These are the lines through x outside x^⊥.
- Counts: every point is on q+2 lines, every line has q points; there are q^3 points and (q+2)q^2 lines.

Check: as_gq.py checks every GQ axiom by brute force, and that the incidence graph has diameter 4, for q = 3, 5, 7, 9, 11, 13.

## 2. Theorem A: two elliptic quadrics make a weighted 2-ovoid

Definition: a weighted m-ovoid of a GQ is a function w from points to {0,1,2,...} with Σ_{p∈L} w(p) = m for every line L.

Setting: let q be odd and ε a non-square in GF(q). Let N(b,c) = b^2 - εc^2, which is anisotropic. For c ≠ 0 let Q_c = {(cN(w), w) : w ∈ GF(q)^2}. Together with x, this is the elliptic quadric v0v1 = cN(v2,v3).

**Theorem A.** If c1·c2 = 1/(4ε), the multiset Q_{c1} + Q_{c2} is a weighted 2-ovoid of AS(q). The two sets share only e = (0,0,0), which gets weight 2; every other point gets weight 0 or 1.

Proof:
1. Fibres: each Q_c has exactly one point over each w, so every fibre gets 1 + 1.
2. Take the coset line through (a0,w0) in direction d, and let D = det(w0,d). Let B = N(w0+d) - N(w0) - N(d).
3. The point with parameter λ lies in Q_c exactly when c·N(d)λ^2 + (cB - D)λ + cN(w0) - a0 = 0. Since N(d) ≠ 0, this is a genuine quadratic.
4. For N = b^2 - εc^2, one checks B^2 - 4N(w0)N(d) = 4εD^2. So the discriminant is Δ_c = 4cN(d)(a0 - a*_c), where a*_c = -(4εcD^2 - 2BD + D^2/c)/(4N(d)).
5. a*_{c1} = a*_{c2} exactly when c1c2 = 1/(4ε). When D = 0, both are 0. Call the common value a*.
6. With χ the quadratic character (χ(0) = 0), the number of roots is 1 + χ(Δ_c). So the line meets the two sets in 2 + χ(N(d)(a0 - a*))·(χ(c1) + χ(c2)) points.
7. χ(c1c2) = χ(ε) = -1, so χ(c1) + χ(c2) = 0, and the count is 2. ∎

(Main session, 2026-10-18: proof checked by hand, including the identity in step 4 and the double-root case.)

**Corollary A1.** For every odd prime power q, n_b(q+2, 4) ≥ 2q^2(q+2), from a (q+2)-regular graph.

Proof of A1:
- Add one new point per entry of Q_{c1} + Q_{c2}, joined to all q+2 lines through its point. Every line gains exactly 2 neighbours.
- A copy v' has the same neighbours as v, so d(v', u) ≤ max(d(v,u), 2). The diameter stays 4.
- Order: q^3 + (q+2)q^2 + 2q^2 = 2q^2(q+2).

Computer check:
- as_w2.py checks the line sums and the graph for q = 3, 5, 7, 9, 11 and 13 (orders 90, 350, 882, 1782, 3146, 5070).
- verify_record.py passes on 1782, 3146 and 5070.

Weights are essential:
- The ILP (movoid_ilp.py, HiGHS) proves AS(q) has no m-ovoid without repeated points for q = 3 (m = 1, 2) or q = 5 (m = 1, 2, 3, 4).
- At q = 5 the largest partial 2-ovoid has 49 points, proved optimal. With repeats allowed the ILP reached 50, in exactly the shape of Theorem A. That is how I found the construction.

Comparison: against Delorme's family (2q^3 + 3q^2 + 3q + 6), A1 is larger by q^2 - 3q - 6, which is positive for every q ≥ 5. At q = 5 it gives 350, below our 359 at (7,4).

## 3. Theorem B: copies with stand-ins (any GQ)

Setup: let S be a GQ of order (s,t) and Δ ≥ max(s,t) + 1.
- Point copies: each point p gets w(p) ≥ 0 copies, each joined to all original lines through p.
- Line copies: a multiset M of lines. A copy y_L is joined, for every p ∈ L, to one stand-in σ_L(p). The stand-in is p itself or one of p's copies.

**Theorem B.**
1. The graph is bipartite with diameter at most 4. It is exactly 4 if S has two non-collinear points.
2. The maximum degree is at most Δ exactly when both of these hold:
   - every line L has Σ_{p∈L} w(p) ≤ Δ - s - 1;
   - every point p is on at most (Δ - t - 1)(1 + w(p)) entries of M. Each of its 1 + w(p) stand-ins serves at most Δ - t - 1 copies.
3. The order is (s+t+2)(st+1) + Σw + |M|.

Proof. Degrees follow by counting. For distances: pairs not involving a line copy are covered by the copy argument (a copy has the same neighbours as its original). A stand-in of r is adjacent to every original line through r.
- Point (original or copy) of p to y_M, need ≤ 3. If p ∉ M, let r be the unique point of M collinear with p, on line K. The path is p-K-σ_M(r)-y_M. If p ∈ M, pick r ∈ M with r ≠ p; the path is p-M-σ_M(r)-y_M.
- Original line L to y_M, need ≤ 4. If L meets M in r (or L = M): L-σ_M(r)-y_M. If they are disjoint: L-s-K-σ_M(r)-y_M, where s ∈ L and r ∈ M are collinear on K.
- y_L to y_M, need ≤ 4. If they share r (or L = M): y_L-σ_L(r)-K-σ_M(r)-y_M, with K any original line through r. If disjoint: the same, with collinear s ∈ L and r ∈ M. ∎

What it covers: Delorme's ovoid copies, the line-multiset theorem in research/gq4/THEOREM.md (all stand-ins original), and the gq_share variant. The dual statement (line copies with weights, point copies using line stand-ins) follows by applying it to the dual GQ.

Test: as_share.py implements it for AS(q) (joint ILP plus a builder that assigns stand-ins). At q = 5, Δ = 8 it used 29 line copies, more than a spread allows without stand-ins, and passed lib.is_valid (graphs/as_share_q5_k1_n404.json, not a record cell).

**Corollary B1 (exact covers give 2Δ(st+1)).** Suppose S has a weighted (Δ-s-1)-ovoid W and a weighted (Δ-t-1)-cover M (every point on exactly Δ-t-1 entries of M, all stand-ins original). Then n_b(Δ,4) ≥ 2Δ(st+1).
- Counting: |W| = (Δ-s-1)(st+1) and |M| = (Δ-t-1)(st+1).
- The total is (st+1)(s+t+2 + 2Δ - s - t - 2) = 2Δ(st+1).
- So Q(4,q) gives 2Δ(q^2+1) and AS(q) gives 2Δq^2.

**Corollary B2 (all degrees).** For every prime power q and every Δ ≥ q+1, n_b(Δ,4) ≥ 2q^2Δ.
- q odd, Δ odd: AS(q) with (Δ-q)/2 copies of Q_{c1} + Q_{c2} (a weighted (Δ-q)-ovoid) and Δ-q-2 copies of the fibre spread (a (Δ-q-2)-cover). B1 gives 2q^2Δ.
- q odd, Δ even: Q(4,q) with j = Δ-q-1, which is even. Bamberg-Law-Penttila's m-ovoids of W(3,q) (m even) are j-covers of Q(4,q). Take j copies of an ovoid (a weighted j-ovoid). B1 gives 2(q^2+1)Δ. (j = 0 is the Moore graph.)
- q even: Q(4,q) has a spread and an ovoid. j copies of each give 2(q^2+1)Δ for every j ≥ 0.

In the table range: odd Δ with Δ-1 not a prime power uses AS(Δ-2) (Δ = 7, 11, 13, 15). The only even such cell is Δ = 16, which uses Q(4,13) with a 2-cover (5440, not yet explicit).

(Main session: parameter counts in B1 and both odd-q cases of B2 checked by hand.)

## 4. The (16,4) construction, precisely

**Proposition.** Let q be odd and O a partial ovoid of AS(q) (no two points on a line). Then n_b(q+3, 4) ≥ 2q^3 + 5q^2 + |O|.
- Construction: AS(q), one copy per entry of Q_{c1} + Q_{c2} + O, and one copy of each fibre (a spread of q^2 lines).
- Lines gain at most 3 neighbours and points gain exactly 1. Theorem B (all stand-ins original) applies.
- Order: q^3 + (q+2)q^2 + 2q^2 + |O| + q^2 = 2q^3 + 5q^2 + |O|.

At q = 13:
- O has 86 points, found by tabu search (ls_cap.c); 87-88 were not reached.
- Order 5325 (graphs/as_deg3_q13_n5325.json). verify_record.py passes, with degrees {13, 15, 16} and sides 2621 + 2704.

Limits of this route:
- Stand-ins don't help. With these point copies fixed, the ILP proves the most line copies is 169 (fixedw_m_ilp.py). So a spread is already the best line set.
- A better point set is a weighted partial 3-ovoid. The best found is a plain set of 428 (ls_cap.c, cap 3), which would give 5329 (not built).
- Matching 5357 needs at least 457. A full weighted 3-ovoid (507) would give 5408. The ceiling with stand-ins is 3q^2 + (q^3 + 3q^2)/q extra, i.e. 5447.
- Weighted 3-ovoids exist for q = 5 and 7 (ILP; ls_wovoid.c finds them in under a second). None was found for q = 9 (ILP 20 minutes, tabu best cost 76), q = 11 (tabu 310) or q = 13 (ILP 30 minutes, tabu 638).
- No symmetric shortcut: a weighted 3-ovoid invariant under (a,w) -> (N(ζ)a, ζw) must be Σ y_k Q_k. The lines through e then force Σ y_k χ(k) = 0, so Σ y_k is even, not 3.
- A joint ILP over both copy sets was too large: it reached 5037 in 40 minutes with a useless bound.
- Conclusion: at (16,4) the Q(4,13) side wins (5357 now, 5440 with an exact 2-cover).

## 5. How far each family can go (Δ = q+2)

- AS(q) plus copies: the Theorem A graph is regular, so 2q^2(q+2) is the maximum, stand-ins included.
- Q(4,q) plus copies, with stand-ins:
  - lines take at most one point copy, so |W| ≤ q^2+1;
  - each line copy needs at least q points that have no copy, so |M| ≤ q^2+1;
  - total at most 2(q^2+1)(q+2), which is 2q+4 above AS;
  - without sharing, Tallini's bound s ≤ q^2-q+1 gives at most 2q^3+4q^2+q+4. So AS is not proved best among all GQ copy graphs.
- q = 5: the Q(4,5) family with one ovoid copy and stand-ins is exactly 21 copied lines (q4_share_ilp.py, HiGHS optimal), so 359 is the maximum of that family. Every ovoid of Q(4,p) is an elliptic quadric (Ball-Govaerts-Storme; from memory), so the choice of ovoid doesn't matter.
- q = 9, 11, 13: matching AS would need 60, 96 and 140 copied lines. The best Q(4,q) searches found 52, 72 and 92.

## 6. Other leads

Other quadrangles:
- Q(5,q), H(3,q^2) and H(4,q^2) have max degree q^2+1 or q^3+1. Those cells already hold Moore graphs, and these GQs give about q^5 vertices against 2q^6. Only orders with s ≈ t matter.
- T2*(O) (q even) has genuine ovoids: affine planes whose line at infinity misses the hyperoval. It gives 2q^2(q+2), but only at Δ = 4, 6, 10, 18, ..., which are Moore cells or out of range.

Hexagons:
- Feit-Higman requires st to be a square, and (q-1)(q+1) never is. So there is no hexagon analogue of AS.
- For (7,6), H(5) would need a distance-2 ovoid and spread; weights don't help at j = 1. The parked attempt (research/gh6) reached 8820, below the table's 8992.

Octagons:
- Order (2,4) = (q-1, q+1) at q = 3 exists: the Ree-Tits octagon GO(2,4), with 1755 points of degree 5 and 2925 lines of 3 points.
- A weighted 2-ovoid on its points would give a 5-regular, diameter-8 graph of order 5850.
- Not pursued. I didn't find the (5,8) table value. From the known neighbours ((4,7) = 840, (4,8) = 2184, (5,7) = 3110), it is likely around 10,000. That is an estimate.

## 7. Literature

- Delorme 1985 (above): ovoid-type duplication in GQ incidence graphs.
- Bamberg, Law, Penttila, Combinatorica 29 (2009) 1-17, https://link.springer.com/article/10.1007/s00493-009-2179-x (abstract): m-ovoids of W(3,q), q odd, every even m.
- Bamberg, Kelly, Law, Penttila, JCTA 114 (2007): an m-ovoid and an i-tight set meet in mi points.
- Feng, Li, arXiv:1908.10659: point-regular groups of P(W(q),x).
- Not found: m-ovoids or weighted ovoids of AS(q), and the bipartite D=6/D=8 table columns. arXiv:1010.5651 (Feria-Purón & Pineda-Villavicencio) has only defect catalogues, no table of largest graphs.

## 8. What was verified by computer

- GQ axioms and diameter 4 of AS(q), q = 3..13 (as_gq.py).
- Theorem A line sums and lib.is_valid for q = 3..13 (as_w2.py); verify_record.py (all three checkers) on 1782, 3146, 5070 and 5325.
- No m-ovoid without repeats: q = 3 (m = 1, 2) and q = 5 (m = 1..4), ILP-proved. Largest partial 2-ovoid of AS(5) = 49, largest partial ovoid of AS(5) = 16, ILP-proved.
- Weighted 3-ovoids exist for q = 5 and 7; none found for q = 9, 11, 13.
- Q(4,5) with one ovoid copy and stand-ins: optimum 21 lines (359).
- For the fixed (16,4) point copies, line copies ≤ 169 (ILP bound).

## 9. Files (research/gq4x/)

- Code: as_gq.py, as_w2.py, as_deg3.py, as_share.py, fixedw_m_ilp.py, q4_share_ilp.py, movoid_ilp.py, ls_cap.c, ls_wovoid.c, export_inst.py.
- Graphs:
  - records: as_w2_q9_n1782.json, as_w2_q11_n3146.json, as_w2_q13_n5070.json;
  - (16,4): as_deg3_q13_n5325.json;
  - checks of other q (3, 5, 7), the q = 5 stand-in test (as_share_q5_k1_n404.json) and q4_share_q5_n359.json;
  - verify_as_w2.txt and verify_as_deg3_q13.txt.
- I deleted the compiled binaries and the runs/*.inst instance files; rebuild them with `cc -O2` and export_inst.py. runs/ keeps the ILP and search logs.

## 10. Next steps

1. Write Theorem A up as a note. It is a short finite-field identity plus the copy lemma, and a good Lean target.
2. (16,4): find an exact 2-cover of Q(4,13) (5440).
3. (7,4): look for structures beyond Q(4,5) with one ovoid copy; AS(5) is capped at 350.
4. Find out whether weighted 3-ovoids of AS(q) exist for q ≥ 9.
