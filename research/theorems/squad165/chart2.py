#!/usr/bin/env python3
"""Charts over F_4^4 that are universal (every nonbacktracking walk of length 4 nonsingular, chart.py) AND
pencil-complete: for every ordered pair of distinct colours (i, j), the 8 vectors
   A-side: {A_i A_k^-1 b_k : k != i} u {b_l : l not in {i,j}} u {A_j A_k^-1 b_k : k != j}
   B-side: {A_i^-1 b_k : k != i}    u {c_l : l not in {i,j}} u {A_j^-1 b_k : k != j}    (c_l = A_l^-1 b_l)
meet all 5 hyperplanes through W = <b_i, b_j> (A side), resp. W' = <c_i, c_j> (B side), i.e. their images in F^4/W
represent all 5 points of PG(1,4).  Then every same-side controller pair at distance 2 is covered in the lift by
once-backtracking walks of length 4, so the controller only needs bipartite diameter <= 5 and a 4-cycle through every
vertex.  usage: python3 chart2.py seconds seed [out.json]"""
import sys, random, time, json
from chart import mat_vec, mat_inv, MUL, INV, vid, span2, violations as univ_violations, rand_gl, rand_vec

def span_mask(vecs):
    """bitmask of the F_4-span of vecs"""
    S = {(0, 0, 0, 0)}
    for v in vecs:
        S = {tuple(a ^ MUL[l][b] for a, b in zip(s, v)) for s in S for l in range(4)}
    m = 0
    for s in S: m |= 1 << vid(s)
    return m, len(S)

def pencil_ok(W, zs):
    """W: list of 2 vectors spanning a 2-dim space; zs: vectors.  True iff the hyperplanes W + <z> include all 5."""
    wm, wn = span_mask(W)
    if wn != 16: return False
    hyps = set()
    for z in zs:
        hm, hn = span_mask(W + [z])
        if hn == 64: hyps.add(hm)
    return len(hyps) == 5

def pencil_violations(A, b):
    Ai = [mat_inv(M) for M in A]
    c = [mat_vec(Ai[l], b[l]) for l in range(4)]
    bad = 0
    for i in range(4):
        for j in range(4):
            if i == j: continue
            zA = [mat_vec(A[i], mat_vec(Ai[k], b[k])) for k in range(4) if k != i] + \
                 [b[l] for l in range(4) if l not in (i, j)] + \
                 [mat_vec(A[j], mat_vec(Ai[k], b[k])) for k in range(4) if k != j]
            if not pencil_ok([b[i], b[j]], zA): bad += 1
            zB = [mat_vec(Ai[i], b[k]) for k in range(4) if k != i] + \
                 [c[l] for l in range(4) if l not in (i, j)] + \
                 [mat_vec(Ai[j], b[k]) for k in range(4) if k != j]
            if not pencil_ok([c[i], c[j]], zB): bad += 1
    return bad

def total(A, b):
    u = univ_violations(A, b)
    if u >= 10 ** 6: return u
    return u + 3 * pencil_violations(A, b)

def search(seconds, seed):
    rng = random.Random(seed)
    I4 = [[int(r == c) for c in range(4)] for r in range(4)]
    best = None; t0 = time.time()
    while time.time() - t0 < seconds:
        A = [I4] + [rand_gl(rng) for _ in range(3)]
        b = [rand_vec(rng) for _ in range(4)]
        cst = total(A, b); stall = 0
        while stall < 300 and cst > 0 and time.time() - t0 < seconds:
            A2 = [[r[:] for r in M] for M in A]; b2 = list(b)
            if rng.random() < 0.5:
                k = rng.randrange(1, 4); A2[k][rng.randrange(4)][rng.randrange(4)] = rng.randrange(4)
                if mat_inv(A2[k]) is None: continue
            else:
                b2[rng.randrange(4)] = rand_vec(rng)
            c2 = total(A2, b2)
            if c2 <= cst:
                stall = 0 if c2 < cst else stall + 1; A, b, cst = A2, b2, c2
            else:
                stall += 1
        if best is None or cst < best[0]:
            best = (cst, A, b); print('best', cst, flush=True)
        if cst == 0: break
    return best

if __name__ == '__main__':
    cst, A, b = search(float(sys.argv[1]), int(sys.argv[2]))
    print('total violations', cst, 'universal', univ_violations(A, b), 'pencil', pencil_violations(A, b))
    if len(sys.argv) > 3 and cst == 0:
        json.dump({'field': 'F4 as 0,1,w,w^2 = 0,1,2,3 (a+bw -> a+2b), addition XOR', 'A': A, 'b': [list(v) for v in b],
                   'properties': 'universal NB-4 and pencil-complete (chart2.py)'}, open(sys.argv[3], 'w'))
        print('written', sys.argv[3])
