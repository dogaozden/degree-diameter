# c14 NOTE: upper bounds for D = 11, 12 and the odd-D Haar criterion

## (a) Upper bounds for bipartite (Delta, D), Delta = 11..14, D = 11, 12

Bipartite Moore bound M = 2 * sum_{i<D} (Delta-1)^i (matches TABLE.md and LITERATURE.md item 15).

Known non-existence results (from search snippets and the arXiv abstract page; full texts not read, so treat as [B]/[V-abstract]):
- Pineda-Villavicencio, "Non-existence of bipartite graphs of diameter at least 4 and defect 2", J. Algebraic Combin.
  34(2) (2011). No bipartite (Delta, D, -2) graphs for D >= 4.
- Feria-Puron, Pineda-Villavicencio, "On bipartite graphs of defect at most 4", Discrete Appl. Math. 160 (2012)
  140-154, arXiv:1010.5651. Proves no bipartite defect-4 graphs for Delta >= 3 and odd D >= 7. Conjectures none for
  Delta >= 3, D >= 5 (open for even D).
- Feit-Higman (1964), as in LITERATURE.md item 16: no Moore bipartite graph (defect 0) for D = 11, 12 with Delta >= 3.
- Parity (proved here): a Delta-regular bipartite graph has equal sides, so its order is even, and M is even. The
  defect is therefore even. Defects 1, 3, 5 are impossible for the regular case.

Consequence for the table:
- D = 11 (odd, >= 7): defects 0, 2, 4 are excluded, so order <= M - 6. The "minus 6" value is justified for D = 11.
- D = 12 (even): defects 0 and 2 are excluded, and defect 4 is only conjectured to be excluded. The proven bound is
  M - 4, not M - 6. "M - 6" for D = 12 would rely on the open conjecture.
- The 2012 paper itself does not state "M - 6"; that value is the combination above.

| Delta | D | M | M-4 (proven, D=12) | M-6 (proven, D=11) |
|---|---|---|---|---|
| 11 | 11 | 22,222,222,222 | - | 22,222,222,216 |
| 12 | 11 | 57,062,334,122 | - | 57,062,334,116 |
| 13 | 11 | 135,092,431,034 | - | 135,092,431,028 |
| 14 | 11 | 298,693,399,006 | - | 298,693,399,000 |
| 11 | 12 | 222,222,222,222 | 222,222,222,218 | - |
| 12 | 12 | 627,685,675,344 | 627,685,675,340 | - |
| 13 | 12 | 1,621,109,172,410 | 1,621,109,172,406 | - |
| 14 | 12 | 3,883,014,187,080 | 3,883,014,187,076 | - |

Not checked: whether a more recent paper improves these for D = 11, 12 (the search was limited).

## (b) Odd-D criterion for Haar graphs

Setup: H(G,S), vertices (g,A), (g,B), edges (g,A) ~ (sg,B). Let X = S^-1 S, Y = S S^-1.
G acts on the right, transitively on each side.

Walks from (1,A): after 2t steps you are at (x,A) with x in X^t (product s_{2t}^-1 s_{2t-1} ... s_2^-1 s_1), and every such
product is realised. So dist((1,A),(x,A)) = min{2t : x in X^t}. Since e in S gives e in X, X^t is increasing in t.
Walks from (1,B): after 2t steps you are at (y,B) with y in Y^t, and dist((1,B),(y,B)) = min{2t : y in Y^t}.
Odd cross distances: dist((1,A),(y,B)) = min{2t+1 : y in S X^t}, and S X^t = Y^t S.

Claim: for D = 2t+1, diam H(G,S) <= D iff X^t = G and Y^t = G.

Proof. Necessity: the A-A pairs from (1,A) need X^t = G (the even distance is at most D-1 = 2t). The B-B pairs from
(1,B) need Y^t = G. Sufficiency: by transitivity on each side, the A-A and B-B pairs are covered by the two conditions.
For A-B pairs, if X^t = G then S X^t = SG = G, and if Y^t = G then Y^t S = G. Either one gives all cross pairs within
distance 2t+1 <= D. So diam <= D.

Consequences: the two conditions are needed separately when G is non-abelian (both are automatic when G is abelian, since
then X = Y). Either condition alone gives the cross pairs, so the minimal correct check is both same-side BFS checks:
one from a single A-vertex (all of X^t = G) and one from a single B-vertex (all of Y^t = G). For even D the criterion
is different and is not covered here.

Counterexample (both needed). G = D6 (dihedral of order 12, given as permutations of 6 points, written as images of 0..5), and
S = {(0,1,2,3,4,5), (0,5,4,3,2,1), (1,0,5,4,3,2), (1,2,3,4,5,0), (3,2,1,0,5,4), (3,4,5,0,1,2)}
(found by minimal_example.py). With |S| = 6 and t = 1 (D = 3):
- X = S^-1 S = G (12 elements), but Y = S S^-1 has only 11 elements.
- BFS diameter of H(D6, S) is 4 > 3, so the diameter is not <= 3, consistent with the criterion.
The same happens for A4 with |S| = 6. Smaller S (|S| <= 5) with a one-sided cover did not occur in S3, D4, Q8, A4, D6.

## Computational checks (all in this folder)
- check_sets.py: for S3, D4, A4, Q8, SL(2,3) and all S containing e with |S| <= 4, t = 1, 2: the criterion agrees with
  BFS diameter in 100% of cases (0 disagreements; 50 + 126 + 462 + 126 + 4094 checks).
- search_onesided.py: random S (|S| 2..7, t up to 4) in D5, D6, D7, S4, A4, SL(2,3), PSL(2,7): one-sided covers
  occur in D6, D7, A4, SL(2,3), PSL(2,7), never in D5 or S4 (3000 samples each).
- minimal_example.py: exhaustive search for the smallest one-sided example, with BFS diameter. Output: D6, |S| = 6, t = 1.

Haar graph order is 2|G|. These checks are on tiny groups and make no claims about real-scale searches (haar_big0 was
not used).
