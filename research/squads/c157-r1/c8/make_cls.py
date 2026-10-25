#!/usr/bin/env python3
"""Convert a d7hex solution (research/d15D7 format) to the class format read by kcls.c.

usage: make_cls.py SRC.sol MODE OUT.cls [EXTRA.txt]
  MODE full: every flag a gives classes (p_a, j) for j = 1,2,3 (t = 3a + j - 1); hub pairs (3a, 3b) for each
             original hub edge (a, b)  -> reproduces kcopy_hub.c (expect OK, +6K vertices).
  MODE j1:   every flag gives only class (p_a, 1) (t = a); hub pairs (a, b) for each original hub edge.
  EXTRA.txt (optional, appended in both modes): lines "p j" = extra classes (no hub edges unless listed as "p j t s").
"""
import sys

N = 177156
Q = 7


def main():
    src, mode, out = sys.argv[1], sys.argv[2], sys.argv[3]
    extra = []
    if len(sys.argv) > 4:
        for ln in open(sys.argv[4]):
            tok = ln.split()
            if tok:
                extra.append(tuple(int(x) for x in tok))
    lines = open(src).read().split('\n')
    hdr = lines[0].split()
    assert hdr[0] == 'd7hex' and int(hdr[1]) == 11 and int(hdr[2]) == N, hdr
    K = int(hdr[3])
    freed = [int(x) for x in lines[1].split()[1:]]
    assert len(freed) == K, (len(freed), K)
    hub = lines[2].split()
    assert hub[0] == 'hubedges'
    m = int(hub[1])
    pairs = [(int(hub[2 + 2 * i]), int(hub[3 + 2 * i])) for i in range(m)]
    M = [int(x) for x in ' '.join(lines[3:]).split()]
    assert len(M) == N, len(M)

    if mode == 'full':
        classes = [(freed[a], j) for a in range(K) for j in (1, 2, 3)]
        hp = [(3 * a, 3 * b) for (a, b) in pairs]
    elif mode == 'j1':
        classes = [(freed[a], 1) for a in range(K)]
        hp = list(pairs)
    else:
        raise SystemExit('mode must be full or j1')
    base_T = len(classes)
    # extra classes: "p j" (no hub-graph edges) or "p j t s" meaning Z_t ~ W_s with t,s = class indices
    for e in extra:
        if len(e) == 2:
            classes.append((e[0], e[1]))
        else:
            classes.append((e[0], e[1]))
            hp.append((e[2], e[3]))
    T = len(classes)
    NV = 2 * Q * N + 2 * T
    with open(out, 'w') as f:
        f.write('d7cls 11 %d %d %d\n' % (N, T, NV))
        for p, j in classes:
            f.write('%d %d\n' % (p, j))
        f.write('hubedges %d\n' % len(hp))
        for t, s in hp:
            f.write('%d %d\n' % (t, s))
        for i in range(0, N, 16):
            f.write(' '.join(str(x) for x in M[i:i + 16]) + '\n')
    print('wrote %s: classes %d (base %d), hub edges %d, NV %d' % (out, T, base_T, len(hp), NV))


if __name__ == '__main__':
    main()
