#!/usr/bin/env python3
"""Referee checks of Lemmas 4.1-4.3 of D7_THEOREMS.md on small cases, with own code (hexlib.py for H(s), PG(2,s) below).
Each graph is written as an edge list with colour class A = 0..K1-1, B = K1..K1+K2-1 and checked by bfsd.c, which
prints the largest same-colour and different-colour distances and the degree range.
Usage: hubtests.py <case> <out.edges>"""
import sys, random, itertools
from hexlib import Hexagon
random.seed(7)

def hexpart(s, copiesA=None, copiesB=None):
    """Lemma 4.1: H(s) with point x replaced by copiesA[x] copies, line l by copiesB[l] copies; returns (KA, KB, edges)"""
    H = Hexagon(s); n = H.N
    cA = copiesA or [1]*n; cB = copiesB or [1]*n
    offA = [0]; [offA.append(offA[-1] + c) for c in cA]
    offB = [0]; [offB.append(offB[-1] + c) for c in cB]
    E = []
    for li, L in enumerate(H.lines):
        for p in L:
            for i in range(cA[p]):
                for j in range(cB[li]): E.append((offA[p] + i, offB[li] + j))
    return offA[-1], offB[-1], E

def pg2(s):
    pts = [v for v in itertools.product(range(s), repeat=3) if any(v) and v[[i for i in range(3) if v[i]][0]] == 1]
    E = [(i, j) for i, p in enumerate(pts) for j, l in enumerate(pts) if sum(a*b for a, b in zip(p, l)) % s == 0]
    return len(pts), E

def treepart(s, delta, cP, cL, gP, gL):
    """Lemma 4.3: PG(2,s) incidence graph, cP pendants at points, cL at lines (<= t = delta-s-1 per core vertex),
    gP pendants below the point-pendants and gL below the line-pendants (<= u = delta-1 per vertex).
    Colour A = points + line-pendants + depth-2 below point-pendants; colour B = lines + point-pendants + ..."""
    n, E0 = pg2(s); t = delta - s - 1; u = delta - 1
    assert cP <= n*t and cL <= n*t and gP <= u*cP and gL <= u*cL
    A = list(range(n)); B = list(range(n))           # A: points, B: lines (local ids)
    E = list(E0)
    KA, KB = n, n
    pendP = []                                       # pendants at points: colour B
    for i in range(cP):
        b = KB; KB += 1; E.append((i % n, b)); pendP.append(b)
    pendL = []
    for i in range(cL):
        a = KA; KA += 1; E.append((a, i % n)); pendL.append(a)
    for i in range(gP):                              # below point-pendants (colour B): colour A
        a = KA; KA += 1; E.append((a, pendP[i % cP]))
    for i in range(gL):
        b = KB; KB += 1; E.append((pendL[i % cL], b))
    return KA, KB, E

def gsum(parts):
    """Lemma 4.2: parts in order; for i < j injections A_j -> B_i and B_j -> A_i"""
    offA = [0]; offB = [0]
    for (a, b, e) in parts: offA.append(offA[-1] + a); offB.append(offB[-1] + b)
    E = []
    for i, (a, b, e) in enumerate(parts): E += [(offA[i] + x, offB[i] + y) for (x, y) in e]
    for i in range(len(parts)):
        for j in range(i + 1, len(parts)):
            ai, bi, _ = parts[i]; aj, bj, _ = parts[j]
            assert aj <= bi and bj <= ai, 'order condition'
            imgB = random.sample(range(bi), aj); imgA = random.sample(range(ai), bj)
            E += [(offA[j] + x, offB[i] + imgB[x]) for x in range(aj)]
            E += [(offA[i] + imgA[y], offB[j] + y) for y in range(bj)]
    return offA[-1], offB[-1], E

def write(K, out):
    KA, KB, E = K
    with open(out, 'w') as f:
        f.write('%d %d\n' % (KA + KB, len(E)))
        for (a, b) in E: f.write('%d %d\n' % (a, KA + b))
    print('wrote %s: %d + %d vertices, %d edges' % (out, KA, KB, len(E)))

case, out = sys.argv[1], sys.argv[2]
if case == 'blow2':      # H(2), each element 1..3 copies (c = 3): degree <= 9, same <= 6, different <= 5
    write(hexpart(2, [random.randint(1, 3) for _ in range(63)], [random.randint(1, 3) for _ in range(63)]), out)
elif case == 'blow3':    # H(3), 1..2 copies
    write(hexpart(3, [random.randint(1, 2) for _ in range(364)], [random.randint(1, 2) for _ in range(364)]), out)
elif case == 'sum':      # H(3) + H(2) blown up (c = 2, asymmetric sizes) + H(2) + pendant-tree part on PG(2,2) last
    p1 = hexpart(3)
    p2 = hexpart(2, [2]*63, [2 if i < 40 else 1 for i in range(63)])
    p3 = hexpart(2)
    p4 = treepart(2, 4, 7, 6, 15, 12)
    write(gsum([p1, p2, p3, p4]), out)
elif case == 'tree':     # pendant-tree part alone: same <= 6, different can be 7
    write(treepart(3, 6, 26, 26, 120, 120), out)
elif case == 'treefirst':  # negative control: the tree part not last
    write(gsum([treepart(3, 6, 26, 26, 120, 120), hexpart(2)]), out)
elif case == 'h7h7':     # the (18,7) hub graph of the note: H(7) + H(7), degree 8 + 1 = 9
    write(gsum([hexpart(7), hexpart(7)]), out)
elif case == 'cert16':   # the (16,2) certificate of hubopt.out: H(8)+H(7)+H(5)+H(4)x2[2730]+H(4)x2[2372], degree <= 14
    c4 = [2]*1365
    p5 = hexpart(4, [2]*1007 + [1]*358, [2]*1007 + [1]*358)    # 2372 per colour
    write(gsum([hexpart(8), hexpart(7), hexpart(5), hexpart(4, c4, c4), p5]), out)
