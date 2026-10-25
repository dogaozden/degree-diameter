import sys, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d13D7/tools')
import hexlib
q, lines, coord = hexlib.load('/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin')
def rank_mod(M, p):
    M = [list(map(lambda v: v % p, row)) for row in M]
    r = 0; rows = len(M); cols = len(M[0]) if rows else 0
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i][c] % p: piv = i; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], p - 2, p)
        M[r] = [(v * inv) % p for v in M[r]]
        for i in range(rows):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        r += 1
    return r
idx = [int(l) for l in open('/home/user/degree-diameter/research/squads/d13D7_r2/c6/best_idx.txt') if l.strip() and not l.startswith('#')]
P = coord[idx].tolist()
print('rank of 397 set (F_11):', rank_mod(P, q))
# perpendicular vectors x with B(x,r)=0 for all r: solve linear system
def Bmat(r):
    # B(x,r) = x0 r4 + x4 r0 + x1 r5 + x5 r1 + x2 r6 + x6 r2 - 2 x3 r3 as linear form in x
    return [r[4], r[5], r[6], -2*r[3], r[0], r[1], r[2]]
M = [Bmat(r) for r in P]
print('rank of linear constraints (= rank of the set under B):', rank_mod(M, q))
