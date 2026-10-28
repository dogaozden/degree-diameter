"""domsat.py: k pairwise disjoint dominating classes in the 2-ball hypergraph of H(q) (lines or points), by SAT.
A class D (set of lines, resp. points) is dominating when it meets every 2-ball B2(x) = {x} plus the elements at
distance 2 from x. k disjoint dominating classes give k colours with every 2-ball seeing all of them.
Usage: python3 domsat.py HEXBIN lines|points k [timeout_s]
Writes parts/dom_q{q}_{type}_k{k}.bin (int32 per element: its class, or -1) when SAT."""
import sys
import time
import threading
import numpy as np
from pysat.solvers import Cadical195
from hexlib import Hex


def balls_of(H, typ):
    out = []
    for x in range(H.N):
        b = {x}
        if typ == 'lines':
            for p in H.lines[x]:
                b.update(H.PL[p].tolist())
        else:
            for l in H.PL[x]:
                b.update(H.lines[l].tolist())
        out.append(sorted(b))
    return out


def main():
    H = Hex(sys.argv[1])
    typ, k = sys.argv[2], int(sys.argv[3])
    tmo = float(sys.argv[4]) if len(sys.argv) > 4 else 600
    q, N = H.q, H.N
    balls = balls_of(H, typ)

    def var(e, i):
        return e * k + i + 1
    s = Cadical195()
    for e in range(N):
        for i in range(k):
            for j in range(i + 1, k):
                s.add_clause([-var(e, i), -var(e, j)])
    for x in range(N):
        for i in range(k):
            s.add_clause([var(e, i) for e in balls[x]])
    # symmetry breaking: the 2-ball of element 0 has its first min(k, |ball|) members in classes 0, 1, ... in order
    # is not valid in general (a class may meet the ball twice); we only fix element balls[0][0] in class 0 or none.
    t0 = time.time()
    r = s.solve()
    print(f'q={q} {typ} k={k}: {"SAT" if r else ("UNSAT" if r is False else "TIMEOUT")} ({time.time() - t0:.1f}s)',
          flush=True)
    if r:
        m = set(v for v in s.get_model() if v > 0)
        cls = [-1] * N
        for e in range(N):
            for i in range(k):
                if var(e, i) in m:
                    cls[e] = i
        np.array(cls, dtype=np.int32).tofile(f'parts/dom_q{q}_{typ}_k{k}.bin')
        sizes = np.bincount([c for c in cls if c >= 0], minlength=k)
        print('class sizes', sorted(sizes.tolist()), 'unclassed', cls.count(-1))


if __name__ == '__main__':
    main()
