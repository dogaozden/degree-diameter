#!/usr/bin/env python3
"""Degree-preserving 2-switch annealing on the bipartite graph of a Haar near miss (not a Haar graph any more).
Usage: sw.py TABLE.bin d S_INDICES SECONDS SEED OUT.edges
Cost = number of unordered same-side pairs at distance > 4 (both sides). Target 0 => diameter <= 5.
Vertices: A-side g (0..N-1), B-side N+g. Initial edges (g,A)~(s*g,B) from the table, as in haar_edges.py."""
import struct, sys, time, array, math
import numpy as np

fn, d, S, secs, seed, out = sys.argv[1], int(sys.argv[2]), list(map(int, sys.argv[3].split())), float(sys.argv[4]), int(sys.argv[5]), sys.argv[6]
data = open(fn, 'rb').read(); N = struct.unpack('<i', data[:4])[0]
T = array.array('H'); T.frombytes(data[4:4 + 2 * N * N])
rng = np.random.default_rng(seed)

M = np.zeros((N, N), dtype=np.float32)          # M[a,b]=1 iff (a,A)~(b,B)
for s in S:
    for g in range(N):
        M[g, T[s * N + g]] = 1.0
assert (M.sum(axis=1) == d).all() and (M.sum(axis=0) == d).all()

def uncovered(M):
    """unordered same-side pairs at distance > 4, both sides (even walks of length <= 4)."""
    tot = 0
    for X in (M, M.T):
        Q = (X @ X.T > 0).astype(np.float32)     # same-side pairs at even distance <= 2 (diagonal included)
        R = (Q @ Q) > 0                          # even walks <= 4
        tot += N * N - int(np.count_nonzero(R))
    return tot // 2

def edges_of(M):
    a, b = np.nonzero(M)
    return np.stack([a, b], axis=1)

E = edges_of(M)
cur = uncovered(M)
best = cur; bestM = M.copy()
print(f"init cost {cur} (N={N}, d={d}, S={S})", flush=True)
t0 = time.time(); it = 0; acc = 0
import os
T0, T1 = float(os.environ.get("T0", 60)), float(os.environ.get("T1", 4))
period = 60.0
while True:
    el = time.time() - t0
    if el > secs: break
    # geometric cooling inside each period, then reheat
    phase = (el % period) / period
    temp = T0 * (T1 / T0) ** phase
    i, j = rng.integers(len(E)), rng.integers(len(E))
    a1, b1 = E[i]; a2, b2 = E[j]
    if a1 == a2 or b1 == b2 or M[a1, b2] or M[a2, b1]:
        continue
    M[a1, b1] = 0; M[a2, b2] = 0; M[a1, b2] = 1; M[a2, b1] = 1
    new = uncovered(M)
    it += 1
    delta = new - cur
    if delta <= 0 or rng.random() < math.exp(-delta / temp):
        cur = new; E[i] = (a1, b2); E[j] = (a2, b1); acc += 1
        if cur < best:
            best = cur; bestM = M.copy()
            print(f"  t={el:.0f}s it={it} best={best}", flush=True)
            if best == 0: break
    else:
        M[a1, b2] = 0; M[a2, b1] = 0; M[a1, b1] = 1; M[a2, b2] = 1
print(f"RESULT switch best={best} evals={it} accepted={acc} time={time.time()-t0:.1f} seed={seed}", flush=True)
ea, eb = np.nonzero(bestM)
with open(out, 'w') as f:
    f.write(f"{2*N}\n")
    for a, b in zip(ea, eb):
        f.write(f"{a} {N+b}\n")
