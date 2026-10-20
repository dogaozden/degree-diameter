# Haar graphs at diameters 4, 6, 7, 8 (p4 area d6haar, 2026-10-19/20)

Status: in progress. Updated hourly.

## 1. Diameter condition (proved)

Haar graph H(G, S): vertices G × {A, B}, edges (g, A) ~ (s g, B) for s ∈ S, |S| = Δ. Write T = S⁻¹S, U = SS⁻¹
(both contain e and are closed under inverses).

**Lemma.** H(G, S) has diameter ≤ D if and only if
- D = 2k:   S T^(k−1) = G, that is S S⁻¹ S S⁻¹ ··· S (2k − 1 letters) = G. One condition.
- D = 2k+1: T^k = G and U^k = G.

So D = 4: SS⁻¹S = G. D = 6: SS⁻¹SS⁻¹S = G. D = 7: (S⁻¹S)³ = G = (SS⁻¹)³. (D = 5 gives the d5 lemma (S⁻¹S)² = G =
(SS⁻¹)².)

*Proof.* Right multiplication (g, X) ↦ (gh, X) preserves edges, so it is an automorphism, transitive on each side;
it is enough to look at distances from (e, A) and (e, B). The graph is bipartite with sides G × {A} and G × {B}, so
same-side distances are even and cross distances are odd. A walk from (e, A) alternately multiplies on the left by
some s (A → B) and by some s⁻¹ (B → A), so after 2j steps it is at an element of (S⁻¹S)^j on side A and after 2j+1
steps at an element of S(S⁻¹S)^j on side B. Since e ∈ S⁻¹S these sets grow with j, so they are exactly the balls:
side A within distance 2j is T^j, side B within 2j+1 is S T^j. In the same way, from (e, B): side B within 2j is
U^j and side A within 2j+1 is S⁻¹U^j.

D = 2k: we need T^k = U^k = G (same side, ≤ 2k) and S T^(k−1) = S⁻¹ U^(k−1) = G (cross, ≤ 2k − 1). Now
(S T^(k−1))⁻¹ = T^(k−1) S⁻¹ = S⁻¹ U^(k−1), T^k = S⁻¹ · (S T^(k−1)) and U^k = (S T^(k−1)) · S⁻¹. If S T^(k−1) = G,
all four are G.

D = 2k+1: we need T^k = U^k = G (same side, ≤ 2k) and S T^k = S⁻¹U^k = G (cross, ≤ 2k + 1); the cross conditions
follow from T^k = G and U^k = G. ∎

**Word bound.** Counting non-backtracking words, |G| is at most half the bipartite Moore bound:
D = 2k: |G| ≤ Δ Σ_{j<k} (Δ−1)^(2j); D = 2k+1: |G| ≤ 1 + Σ_{j=1..k} Δ(Δ−1)^(2j−1).

## 2. What the table needs (Combinatorics Wiki bipartite table, fetched 2026-10-19)

Ratio = smallest group order that beats the table / word bound. Our D = 5 Haar records reached 0.27–0.52.

D = 6 (only Δ with a non-Moore entry; all other Δ ≤ 16 are generalized hexagons, Moore, so nothing to beat):
| Δ | table | group order needed | word bound | ratio |
|---|---|---|---|---|
| 7 | 8992 | 4497 | 9331 | 0.482 |
| 11 | 142464 | 71233 | 111111 | 0.641 |
| 13 | 374452 | 187227 | 271453 | 0.690 |
| 15 | 842048 | 421025 | 579195 | 0.727 |
| 16 | 884062 | 442032 | 813616 | 0.543 |

D = 4: Moore except Δ = 7 (346: needs 174 of 259, 0.672), 11 (0.781), 13 (0.813), 15 (0.837), 16 (0.710).

D = 7 (no Moore entries):
| Δ | table | order needed | word bound | ratio |
|---|---|---|---|---|
| 4 | 840 | 421 | 1093 | 0.385 |
| 5 | 3110 | 1556 | 5461 | 0.285 |
| 6 | 8310 | 4156 | 19531 | 0.213 |
| 7 | 23436 | 11719 | 55987 | 0.209 |
| 8 | 40586 | 20294 | 137257 | 0.148 |
| 9 | 117648 | 58825 | 299593 | 0.196 |
| 10 | 224694 | 112348 | 597871 | 0.188 |

D = 8: Δ = 4: 2184 (needs 1093, 0.333); Δ = 5: 9234 (4618, 0.211); Δ = 6: 29790 (14896, 0.153); Δ = 7: 80940
(40471, 0.120); Δ = 8: 201480 (100741, 0.105).

So diameter 6 (and 4) is a poor fit for Haar graphs: the only non-Moore cells need 48–84 % of the word bound. Diameters
7 and 8 need only 10–38 %.

## 3. Search code

`haar_dd.c`: annealing over S (same moves and schedule as research/d5/haar_search3.c, K best-of-sample), any D ≥ 3,
group G0 × Z_c with G0 from a groups.py table (groups.py is a copy of research/d5/groups.py). The cost is the number
of elements missed by the sets of the lemma, computed by deduplicated set products (stamp array), e.g. D = 7:
|T|·|T| + |T²|·|T| products per side. `haar_dd check D d table c seed` compares the cost with a BFS on the graph for
200 random S: agrees on all 144 (D, Δ, group) combinations tested (D = 3..8, Δ = 2..5, six groups, mixed outcomes).
`haar_dd eval` on the (9,5) SL(2,11) record gives cost 0 at D = 5 and BFS diameter 5.

## 4. Runs

(in progress)
