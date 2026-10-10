"""Known graphs for tests."""


def lcf(n, jumps):
    """Cubic graph from LCF notation: a Hamiltonian cycle plus chords."""
    edges = set()
    for i in range(n):
        for j in ((i + 1) % n, (i + jumps[i % len(jumps)]) % n):
            edges.add((min(i, j), max(i, j)))
    return n, sorted(edges)


HEAWOOD = lcf(14, [5, -5])                          # d=3, D=3, 14 vertices (optimal)
TUTTE_COXETER = lcf(30, [-13, -9, 7, -7, 9, 13])    # d=3, D=4, 30 vertices (optimal)
