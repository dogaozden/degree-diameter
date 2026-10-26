#!/usr/bin/env python3
"""Edge list of the Haar graph H(G,S) from a table: haar_edges.py TABLE.bin "s0 s1 ..." OUT.edges
Vertices (g,A) = g, (g,B) = N + g; edges (g,A) ~ (s*g, B). Check with apsp OUT.edges d 5."""
import struct, sys
fn, S, out = sys.argv[1], list(map(int, sys.argv[2].split())), sys.argv[3]
data = open(fn, 'rb').read(); N = struct.unpack('<i', data[:4])[0]
import array
T = array.array('H'); T.frombytes(data[4:4 + 2 * N * N])
with open(out, 'w') as f:
    f.write(f"{2 * N}\n")
    for g in range(N):
        for s in S: f.write(f"{g} {N + T[s * N + g]}\n")
