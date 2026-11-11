#!/usr/bin/env python3
"""tab2edges.py TABLE.bin OUT.edges s1 s2 ...: edge list of the Haar graph H(G,S) from a group table (int32 N, then
N*N uint16, T[s*N+g] = s*g, identity 0). Vertices (g,A) = g, (g,B) = N + g; edges (g,A) ~ (s g, B).
Checks first: T is a Latin square, 0 is the identity, associativity on 200,000 random triples."""
import sys, numpy as np
f = open(sys.argv[1], 'rb'); N = int(np.frombuffer(f.read(4), dtype=np.int32)[0])
T = np.frombuffer(f.read(), dtype=np.uint16).astype(np.int64).reshape(N, N)
ar = np.arange(N)
assert all((np.sort(T[i]) == ar).all() for i in range(N)), "row not a permutation"
assert all((np.sort(T[:, j]) == ar).all() for j in range(N)), "column not a permutation"
assert (T[0] == ar).all() and (T[:, 0] == ar).all(), "0 is not the identity"
rng = np.random.default_rng(1); a, b, c = rng.integers(0, N, (3, 200000))
assert (T[T[a, b], c] == T[a, T[b, c]]).all(), "not associative"
S = [int(x) for x in sys.argv[3:]]
assert len(set(S)) == len(S)
with open(sys.argv[2], 'w') as o:
    o.write(f"{2 * N}\n")
    for s in S:
        for g in range(N): o.write(f"{g} {N + T[s, g]}\n")
print(f"group table ok (N={N}, Latin, identity 0, associative on 200k triples); wrote {2*N} vertices, {len(S)*N} edges")
