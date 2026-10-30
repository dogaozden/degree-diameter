#!/usr/bin/env python3
"""Mixed route-chart base for (7,5): controller C = union of 4 perfect matchings (colours 0..3) on M0+M0 vertices
(M0=4: the K44 controller of build_d8D5_n2048.py), fibre F_2^n (Q=2^n).  Chart colours (lam in F_2, 2 edges per
controller edge) and one plain colour P (single edge u -> A_P u + b_P).  Degree 3*2+1 = 7.
Output: vl base file (no voltages, so vl randomises them) with b = 2*M0*Q vertices; the lift by a group of order g
has 2*M0*Q*g vertices.  usage: build_chart7.py OUT_BASE OUT_PARAMS n M0 seed plain [ctrl=k44|rand] [rand_AB=0|1]
"""
import sys, random, itertools, json

def rank_f2(rows):
    rows = [int(''.join(map(str, r)), 2) for r in rows]; r = 0
    for bit in range(64):
        piv = None
        for k in range(r, len(rows)):
            if rows[k] >> bit & 1: piv = k; break
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        for k in range(len(rows)):
            if k != r and rows[k] >> bit & 1: rows[k] ^= rows[r]
        r += 1
    return r

def mat_vec(M, v):
    return [sum(a * x for a, x in zip(row, v)) % 2 for row in M]

def vid(v): return sum(c << t for t, c in enumerate(v))

def main():
    out, outp = sys.argv[1], sys.argv[2]
    n, M0, seed, plain = int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6])
    ctrl = sys.argv[7] if len(sys.argv) > 7 else 'rand'
    rand_AB = int(sys.argv[8]) if len(sys.argv) > 8 else 1
    rnd = random.Random(seed); Q = 2 ** n
    # controller: 4 colour classes, each a perfect matching; simple graph (no pair gets two colours)
    while True:
        perms = []
        for c in range(4):
            p = list(range(M0)); rnd.shuffle(p); perms.append(p)
        pairs = {(i, perms[c][i]) for c in range(4) for i in range(M0)}
        if len(pairs) == 4 * M0: break
    ctrl_edges = [(i, perms[c][i], c) for c in range(4) for i in range(M0)]
    # fibre maps: invertible A_c, nonzero b_c
    def rand_inv():
        while True:
            M = [[rnd.randint(0, 1) for _ in range(n)] for _ in range(n)]
            if rank_f2(M) == n: return M
    A = [rand_inv() for _ in range(4)]
    B = [[rnd.randint(0, 1) for _ in range(n)] for _ in range(4)]
    for c in range(4):
        while not any(B[c]): B[c] = [rnd.randint(0, 1) for _ in range(n)]
    # plain colour: lam not used (single edge u -> A u + b)
    edges = set()
    vecs = list(itertools.product(range(2), repeat=n))
    nA = M0 * Q
    for (i, j, c) in ctrl_edges:
        lams = [0] if c == plain else [0, 1]
        for u in vecs:
            y0 = mat_vec(A[c], u)
            for lam in lams:
                y = [(p + lam * b) % 2 for p, b in zip(y0, B[c])]
                edges.add((i * Q + vid(u), nA + j * Q + vid(y)))
    edges = sorted(edges)
    b = 2 * nA
    deg = [0] * b
    for a, bb in edges: deg[a] += 1; deg[bb] += 1
    assert all(d == 7 for d in deg), set(deg)
    with open(out, 'w') as f:
        f.write(f"{b} {len(edges)}\n")
        f.write(' '.join(['0'] * nA + ['1'] * nA) + '\n')
        for a, bb in edges: f.write(f"{a} {bb}\n")
    json.dump({'n': n, 'M0': M0, 'seed': seed, 'plain': plain, 'ctrl_edges': ctrl_edges, 'A': A, 'B': B,
               'b': b, 'E': len(edges)}, open(outp, 'w'))
    print('base b', b, 'E', len(edges), 'degree 7 ok')

if __name__ == '__main__':
    main()
