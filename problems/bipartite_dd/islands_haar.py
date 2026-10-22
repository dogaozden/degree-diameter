"""Haar-graph specialist islands for diameter 5 (d6D5, d10D5, d11D5).

Same scoring as islands.Specialist; the prompt additionally teaches the Haar-graph search that produced our D = 5
records (1152, 1764, 2662), so Haiku mutates group-based programs instead of starting from lifts.

Pick one in a config with  problem = "problems.bipartite_dd.islands_haar:D10D5"
"""
from .islands import Specialist

HAAR_NOTES = """

## Haar graphs: how our diameter-5 records were found (read this first)
Our records at d = 7, 8, 9 (1152, 1764, 2662 vertices) are all Haar graphs. Take a finite group G and a connection
set S of d group elements. Vertices (g, A) and (g, B), g in G; edges (g, A) ~ (s*g, B) for s in S. The graph is
bipartite, d-regular, has 2|G| vertices, and every A-vertex (and every B-vertex) looks the same. PROVED: its
diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. So cost(S) = (|G| - |(S^-1 S)^2|) + (|G| - |(S S^-1)^2|)
counts uncovered elements and the graph is valid exactly when the cost is 0. Counting words gives
|G| <= 1 + d(d-1) + d(d-1)^3, and abelian groups waste most words, so use NON-abelian groups: metacyclic Z_m x| Z_k,
SL(2,p) (times Z_k), AGL(1,q) (times Z_k), Heisenberg mod p (times Z_k), PGL(2,p), Z_p^2 x| Z_k.
To beat the record the group order must EXCEED record/2 (the graph has 2|G| vertices).
Records came from annealing S with K random replacements per step and an incremental cost (only the ~4 d^3 words that
involve the changed slot are redone), best-of-K accepted by a Metropolis rule, restarts when stuck. Near misses
(a few elements short) exist just above the thresholds, so more search speed, smarter moves (swap in a conjugate or a
product of two elements, move to a neighbour of an uncovered element), better restarts, and trying other groups of
nearly the same order are all worth trying. Always check the finished graph with lib.is_valid and fall back to a valid
smaller Haar graph; a near miss scores 0. Vertex ids: A-vertex g is g, B-vertex g is N + g.
"""


class HaarSpecialist(Specialist):
    def prompt_context(self):
        return super().prompt_context() + HAAR_NOTES


D6D5 = HaarSpecialist(["d6D5"])
D10D5 = HaarSpecialist(["d10D5"])
D11D5 = HaarSpecialist(["d11D5"])
