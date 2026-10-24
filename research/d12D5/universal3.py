#!/usr/bin/env python3
"""Search for a universal route chart over F_3 (all 216 patterns nonsingular), using the tripod structure.
Notation: C_j = A_j^-1, P_j = C_j b_j.  A-side patterns all nonsingular iff the A-tripods T_j = C_j(tripod at b_j)
partition PG(3,3).  tripods.py: four disjoint tripods must be coplanar, so b_0..b_3 must be a plane frame.  Gauge:
A_0 = I (so T_0 = the tripod at b_0), b = e0, e1, e2, e0+e1+e2.  There are 6 partitions of the complement of T_0 into
three flat tripods, and in all of them the apexes P_0..P_3 are the 4 points of one line l_P.  Then every B-side line
V(j;i) = A_j <P_j, P_i> equals A_j l_P, so the B side is perfect iff the four lines A_j l_P are pairwise skew.
For each partition and each labelling of the tripods' lines (line of T_j labelled i must be C_j <b_j, b_i>), this
enumerates the C_j (coset of the stabiliser of a labelled flat tripod), keeps those with A_j l_P skew to l_P, finds
pairwise skew triples, and evaluates each universal chart's pencil condition with chart3 -p.
usage: python3 universal3.py OUTDIR [max_charts]"""
import sys, os, itertools, subprocess
from tripods import PTS, IDX, LINES, norm, line, rank, tripods, count_partitions
import gf3

b = [(1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (1, 1, 1, 0)]

def mask(pts):
    m = 0
    for i in pts:
        m |= 1 << i
    return m

def apex_and_lines(m):
    P = [i for i in range(40) if (m >> i) & 1]
    for p in P:
        ls = [l for l in LINES if p in l and l <= set(P)]
        if len(ls) == 3:
            return p, ls
    raise ValueError

def cols(vs):
    return [[vs[c][r] for c in range(4)] for r in range(4)]

def scal(v, s):
    return tuple((s * x) % 3 for x in v)

def coset(j, Pj, lab):
    """all C with C b_j ~ P_j and C <b_j, b_i> = lab[i] (a line through P_j) for the three i != j"""
    others = [i for i in range(4) if i != j]
    i1, i2, i3 = others
    w = (0, 0, 0, 1)
    S = cols([b[j], b[i1], b[i2], w]); Si = gf3.mat_inv(S)
    out = []
    L1 = [PTS[x] for x in lab[i1] if PTS[x] != PTS[Pj]]
    L2 = [PTS[x] for x in lab[i2] if PTS[x] != PTS[Pj]]
    for lam in (1, 2):
        cp = scal(PTS[Pj], lam)
        for v1 in L1:
            for s1 in (1, 2):
                for v2 in L2:
                    for s2 in (1, 2):
                        a1, a2 = scal(v1, s1), scal(v2, s2)
                        if rank([cp, a1, a2]) < 3:
                            continue
                        for wv in itertools.product(range(3), repeat=4):
                            if rank([cp, a1, a2, wv]) < 4:
                                continue
                            C = gf3.mat_mul(cols([cp, a1, a2, wv]), Si)
                            if IDX[norm(gf3.mat_vec(C, b[i3]))] in lab[i3]:
                                out.append(C)
    return out

def line_of(vecs):
    return line(vecs[0], vecs[1])

def main():
    outdir = sys.argv[1]; maxc = int(sys.argv[2]) if len(sys.argv) > 2 else 50
    os.makedirs(outdir, exist_ok=True)
    tri = tripods('flat')
    T0 = line(b[0], b[1]) | line(b[0], b[2]) | line(b[0], b[3])
    sols = count_partitions(mask(T0), tri)
    I4 = [[int(r == c) for c in range(4)] for r in range(4)]
    nchart = 0; best = None
    for si, sol in enumerate(sols):
        info = [apex_and_lines(m) for m in sol]                  # tripods T_1, T_2, T_3 (unordered: assign to j)
        lP = line(PTS[IDX[norm(b[0])]], PTS[info[0][0]])
        # T_1..T_3 can be assigned to letters 1..3 in any order
        for assign in itertools.permutations(range(3)):
            cand = {}
            for j in (1, 2, 3):
                Pj, ls = info[assign[j - 1]]
                others = [i for i in range(4) if i != j]
                cand[j] = []
                for perm in itertools.permutations(ls):
                    lab = {others[t]: perm[t] for t in range(3)}
                    for C in coset(j, Pj, lab):
                        A = gf3.mat_inv(C)
                        img = frozenset(IDX[norm(gf3.mat_vec(A, PTS[x]))] for x in lP)
                        if not (img & lP):
                            cand[j].append((img, A))
            # pairwise skew triples
            for (l1, A1) in cand[1]:
                for (l2, A2) in cand[2]:
                    if l1 & l2:
                        continue
                    for (l3, A3) in cand[3]:
                        if l3 & l1 or l3 & l2:
                            continue
                        nchart += 1
                        fn = os.path.join(outdir, 'u_%d_%s_%d.txt' % (si, ''.join(map(str, assign)), nchart))
                        with open(fn, 'w') as f:
                            for M in (I4, A1, A2, A3):
                                f.write(' '.join(str(M[r][c]) for r in range(4) for c in range(4)) + '\n')
                            for v in b:
                                f.write(' '.join(map(str, v)) + '\n')
                        res = subprocess.run(['./chart3', '-p', fn, '/dev/null'], capture_output=True, text=True).stdout
                        first = res.splitlines()[0]
                        sing = int(first.split()[2].rstrip(',')); pen = int(first.split()[5])
                        if best is None or (sing, pen) < best[0]:
                            best = ((sing, pen), fn); print('new best', best, flush=True)
                        if sing + pen == 0:
                            print('UNIVERSAL AND PENCIL-COMPLETE:', fn, flush=True)
                        if nchart >= maxc:
                            print('stopped after', nchart, 'charts; best', best); return
            print(f'partition {si} assign {assign}: candidates per letter', [len(cand[j]) for j in (1, 2, 3)], 'charts so far', nchart, flush=True)
    print('total charts', nchart, 'best', best)

if __name__ == '__main__':
    main()
