"""Random regular tournaments on n=7 vertices (rotational start + reversal of directed 3-cycles)."""
import random
def arcs_random(n, rng, steps=3000):
    arcs = {(j, (j + k) % n) for j in range(n) for k in (1, 2, 3)}
    for _ in range(steps):
        u, v, w = rng.sample(range(n), 3)
        if (u, v) in arcs and (v, w) in arcs and (w, u) in arcs:
            arcs -= {(u, v), (v, w), (w, u)}; arcs |= {(v, u), (w, v), (u, w)}
    return sorted(arcs)
