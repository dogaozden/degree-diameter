"""domcheck.py: scorer for the ball-lift colourings (independent of the search code).

Input: H(q) (hexgen2 .bin), a point colouring and a line colouring (int32 per element; -1 = uncoloured), and the
radius s of the balls (s = 2 for the D = 9 lift, s = 4 for the D = 11 lift). A colour class is GOOD when it meets the
s-ball (elements of the same type at distance <= s in the incidence graph) of every element of that type. The score is
k = the number of colours that are good on both sides, after checking that the good classes can be balanced
(sum over good colours of max(|A_i|, |B_i|) <= N). Prints k and the orders 2N(2rk+1) for r = 1..4.
Usage: python3 domcheck.py HEXBIN POINTCOL LINECOL [s]
"""
import sys
import numpy as np
from hexlib import Hex


def ball_hits(H, col, typ, s):
    """for each colour, whether it meets every s-ball of type typ (BFS on the incidence graph, radius s)."""
    N, q = H.N, H.q
    adj = H.adjacency()
    off = 0 if typ == 'points' else N
    colours = sorted(set(col[col >= 0].tolist()))
    good = {c: True for c in colours}
    full = np.full(2 * N, -1, dtype=np.int64)
    full[off:off + N] = col
    for x in range(N):
        seen = {off + x}
        fr = [off + x]
        for _ in range(s):
            nxt = []
            for v in fr:
                for w in adj[v]:
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
            fr = nxt
        present = set(full[list(seen)].tolist())
        for c in colours:
            if good[c] and c not in present:
                good[c] = False
    return good


def main():
    H = Hex(sys.argv[1])
    cp = np.fromfile(sys.argv[2], dtype=np.int32).astype(np.int64)
    cl = np.fromfile(sys.argv[3], dtype=np.int32).astype(np.int64)
    s = int(sys.argv[4]) if len(sys.argv) > 4 else 2
    N, q = H.N, H.q
    gp = ball_hits(H, cp, 'points', s)
    gl = ball_hits(H, cl, 'lines', s)
    both = [c for c in gp if gp[c] and gl.get(c, False)]
    sizes = sum(max(int((cp == c).sum()), int((cl == c).sum())) for c in both)
    ok = sizes <= N
    k = len(both) if ok else 0
    print(f'q={q} s={s}: good point colours {sum(gp.values())}, good line colours {sum(gl.values())}, '
          f'good on both {len(both)}, balance {"ok" if ok else "FAILS"} -> k = {k}')
    for r in range(1, 5):
        m = 2 * r * k + 1
        print(f'  r={r}: Delta={q + 1 + r}, D={2 * s + 5 if s else 7}, m={m}, order {2 * N * m:,}')


if __name__ == '__main__':
    main()
