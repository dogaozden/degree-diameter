#!/usr/bin/env python3
"""Writes dart files for lift8 (round 3, card c4). Format: lines "a b w" (A index 0..3, B index 0..3, A->B voltage; -1 random).
  python3 make_darts.py record  -> record_darts.txt: the 704-vertex record's Z88 voltages (from records/build_d6D5_n704_z88.py)
  python3 make_darts.py pq P Q  -> base_P_Q.txt with rows [1,0,P,5-P],[0,1,5-P,P],[Q,5-Q,1,0],[5-Q,Q,0,1], voltages -1."""
import sys
def write(path, darts):
    with open(path, "w") as f:
        for a, b, w in darts: f.write(f"{a} {b} {w}\n")
def matrix(darts):
    M = [[0]*4 for _ in range(4)]
    for a, b, w in darts: M[a][b] += 1
    return M
if sys.argv[1] == "record":
    E1 = [(7, 5, 1), (9, 7, 0), (4, 4, 1), (6, 0, 0), (1, 1, 0)]
    E2 = [(7, 1, 1), (8, 0, 1), (6, 1, 0), (9, 0, 1), (5, 4, 0)]
    crt = lambda a, i: next(t for t in range(88) if t % 11 == a and t % 8 == i)
    V = lambda e: (crt(e[0], e[1]), e[2])
    base = []   # (A name index, B name index, voltage A->B mod 88); A0^j -> j, A1^j -> 2+j, B0^j -> j, B1^j -> 2+j
    ai = lambda s, j: (0 if s == 'A0' else 2) + j
    for j in (0, 1):
        base.append((ai('A0', j), j, 0)); base.append((ai('A1', j), 2 + j, 0))
        for e in E1:
            s, l = V(e); base.append((ai('A0', j), 2 + (j + l) % 2, (45**j * s) % 88))
        for e in E2:
            s, l = V(e); base.append((ai('A1', (j + l) % 2), j, (-(45**j * s)) % 88))
    print("matrix", matrix(base))
    write("record_darts.txt", base)
elif sys.argv[1] == "pq":
    P, Q = int(sys.argv[2]), int(sys.argv[3])
    M = [[1, 0, P, 5-P], [0, 1, 5-P, P], [Q, 5-Q, 1, 0], [5-Q, Q, 0, 1]]
    darts = [(a, b, -1) for a in range(4) for b in range(4) for _ in range(M[a][b])]
    print("matrix", M, "darts", len(darts))
    write(f"base_{P}_{Q}.txt", darts)
