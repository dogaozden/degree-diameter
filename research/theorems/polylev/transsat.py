"""transsat.py: a T-equivariant colouring of the points (or lines) of H(q) by Z_k, k = |T|, in which every 2-ball sees
every colour ("dominating transversal": the colour classes are the T-translates of one transversal D_0 of the T-orbits).

T = <h> acts semiregularly (orbits of size k). Each orbit O gets a representative b_O; the element h^j b_O has colour
j + s_O (mod k), with s_O in Z_k unknown. Since B2(h x) = h B2(x), it suffices that the 2-ball of one element per
orbit sees all colours. SAT: y[O][s] one-hot; for each orbit representative x and colour c, some y in B2(x) has c.
Usage: python3 transsat.py HEXBIN PERMFILE lines|points OUT [solver]
Writes OUT (int32 colour per element) when SAT."""
import sys
import time
import numpy as np
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from hexlib import Hex
from domsat import balls_of


def main():
    H = Hex(sys.argv[1])
    perm = np.fromfile(sys.argv[2], dtype=np.int32).astype(np.int64)
    typ, out = sys.argv[3], sys.argv[4]
    sname = sys.argv[5] if len(sys.argv) > 5 else 'cd19'
    N = H.N
    orb = -np.ones(N, dtype=np.int64)
    idx = np.zeros(N, dtype=np.int64)
    reps = []
    for s in range(N):
        if orb[s] >= 0:
            continue
        x, j = s, 0
        while orb[x] < 0:
            orb[x] = len(reps)
            idx[x] = j
            x = perm[x]
            j += 1
        reps.append(s)
    k = j
    n_o = len(reps)
    balls = balls_of(H, typ)
    print(f'q={H.q} {typ}: k={k}, {n_o} orbits, ball size {len(balls[0])}', flush=True)

    def y(o, s):
        return o * k + s + 1
    top = n_o * k
    clauses = []
    for o in range(n_o):
        enc = CardEnc.equals(lits=[y(o, s) for s in range(k)], bound=1, top_id=top, encoding=EncType.seqcounter)
        top = max(top, enc.nv)
        clauses.extend(enc.clauses)
    for o in range(n_o):
        b = balls[reps[o]]
        for c in range(k):
            clauses.append([int(y(int(orb[x]), int((c - idx[x]) % k))) for x in b])
    t0 = time.time()
    with Solver(name=sname) as S:
        for cl in clauses:
            S.add_clause(cl)
        r = S.solve()
        print(f'{"SAT" if r else "UNSAT"} in {time.time() - t0:.1f}s', flush=True)
        if r:
            m = S.get_model()
            s_of = np.zeros(n_o, dtype=np.int64)
            for o in range(n_o):
                for s in range(k):
                    if m[y(o, s) - 1] > 0:
                        s_of[o] = s
            col = (idx + s_of[orb]) % k
            # independent check
            bad = sum(1 for x in range(N) if len(set(col[balls[x]].tolist())) != k)
            print(f'check: 2-balls missing a colour: {bad}')
            col.astype(np.int32).tofile(out)


if __name__ == '__main__':
    main()
