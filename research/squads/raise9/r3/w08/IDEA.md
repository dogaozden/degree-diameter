# w08 IDEA: bi-coset graphs (Haar graphs over a subgroup H), a family none of the rounds tried

Haar graph H(G,S): vertices G x {A,B}, edge (g,A)~(sg,B). Generalisation used here:
side A = left cosets Hx (H <= G), side B = left cosets Ky (K <= G), edge Hx ~ Ky iff x y^-1 in H S K, where S is a union
of H-K double cosets (well defined). Right multiplication by G is an automorphism, transitive on each side, so
diameter = max(ecc(H), ecc(K)) by two BFS. Each side has |G|/|H| vertices (H = K here, |H| = 2): the graph has
2|G|/|H| vertices, and degree = |HSH|/|H| per double coset. So a (3,9) graph on 508 vertices (> 506, the record)
comes from a group of order 508 with H = an involution: the Haar exhaustive (rounds 1-2) only covered N = 254-330
with H trivial, so these 2-to-1 quotients were never searched.

Test plan: (1) all groups of order 2m (metacyclic via groups.py, plus direct table for Z127 x| Z4 etc.), all involutions
H, all unions of double cosets of degree 3 at m = 254 (V = 508), exhaustive with bitset BFS. (2) sanity: independent
APSP check ($B/apsp) of any diameter-9 candidate and of a known diameter-5 example.
