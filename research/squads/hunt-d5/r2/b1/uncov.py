#!/usr/bin/env python3
"""uncov.py TABLE.bin "s0 s1 ..." : cost of H(G,S) side A and side B, and the uncovered elements of each side."""
import struct, sys, array
fn, S = sys.argv[1], list(map(int, sys.argv[2].split()))
data = open(fn, 'rb').read(); N = struct.unpack('<i', data[:4])[0]
MT = array.array('H'); MT.frombytes(data[4:4 + 2 * N * N])
INV = [0] * N
for a in range(N):
    for b in range(N):
        if MT[a * N + b] == 0: INV[a] = b; break
def side(sideB):
    T = set()
    T = set()
    for x in S:
        for y in S:
            T.add(MT[x * N + INV[y]] if sideB else MT[INV[x] * N + y])
    C = set()
    Tl = sorted(T)
    for a in Tl:
        for b in Tl:
            C.add(MT[a * N + b])
    return sorted(set(range(N)) - C)
uA, uB = side(False), side(True)
print(f"cost={len(uA)+len(uB)} sideA_uncovered={len(uA)} {uA}")
print(f"sideB_uncovered={len(uB)} {uB}")
